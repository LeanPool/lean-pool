/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.CatalyticRegisters.PrimeFieldTools

/-!
# Theorem T1: Complete Base-`p` Digit-Sum Dichotomy for 2-Register Passive Programs over `𝔽_p`

We formalize the instruction set of Vinciguerra's Definition 2.2 (2-register passive-output)
with formal-polynomial cleanliness in `𝔽_p[O, R, x]` and `𝔽_p` constants (distinct from functional Def. 2.2 on `𝔽_p`),
and prove the exact unconditional if-and-only-if characterization (**Theorem T1**):

  `f ∈ RP^{pass}_{𝔽_p}(2, t)  ↔  ∀ d ≥ 2, ([x^d] f ≠ 0 mod p) → s_p(d) ≤ min (p - 1) (t - 1)`

for every prime `p`, every input-access budget `t ≥ 1`, and every univariate polynomial
`f ∈ 𝔽_p[x]`.

Immediate machine-checked corollaries:
  1. **Unbounded-degree 2-access Frobenius collapse** (`char_p_two_access_unbounded_degree`):
     `∀ p prime, ∀ m, x^(p^m) ∈ RP^{pass}_{𝔽_p}(2, 2)`, showing `D^{pass}_{2, 𝔽_p}(2) = +∞`
     and showing Vinciguerra's characteristic-0 lower bounds (Theorems 3.2, 3.3, 3.5 of
     `arXiv:2609.18692`) do not extend to positive prime characteristic.
  2. **Exact `𝔽_2` saturation** (`char_2_two_reg_x3_impossible`):
     `∀ t, x^3 ∉ RP^{pass}_{𝔽_2}(2, t)` — over `𝔽_2`, no 2-register `𝔽_2`-const program
     yields the formal polynomial `x^3` for any `t` (as a function on `𝔽_2`, `x^3 = x`).
  3. **Exact prime-field impossibility threshold** (`char_p_impossibility_threshold`):
     whenever `s_p(d) ≥ p`, `x^d ∉ RP^{pass}_{𝔽_p}(2, t)` for EVERY `t`.
  4. **Large-characteristic analogue** (`char_p_large_recovers_vinciguerra_thm35`):
     whenever `2 ≤ d < p`, `x^d ∈ RP^{pass}_{𝔽_p}(2, t) ↔ d + 1 ≤ t` (large-char analogue of
     Vinciguerra's Theorem 3.5; nothing is proved over a characteristic-0 field).
-/

namespace Catalytic

@[expose] public section

/-! ## 1. Literal 2-Register Passive-Output Model over `𝔽_p` (Vinciguerra Def. 2.2) -/

/--
A primitive instruction of a passive-output 2-register program over `𝔽_p`
with registers `(O, R)` (where `O` is passive and never occurs on any RHS):
  * `addOut poly`:     `O ← O + ∑_k poly[k] * R^k`   (basic op, 0 input accesses)
  * `addWorkConst c`:  `R ← R + c`                   (basic op on `R`, 0 input accesses)
  * `addInputOut lam`: `O ← O + lam * x`             (input access to `O`, 1 access)
  * `addInputWork lam`:`R ← R + lam * x`             (input access to `R`, 1 access)
-/
inductive Pass2Instr where
  | addOut (poly : List Nat) : Pass2Instr
  | addWorkConst (c : Nat) : Pass2Instr
  | addInputOut (lam : Nat) : Pass2Instr
  | addInputWork (lam : Nat) : Pass2Instr
  deriving DecidableEq, Repr

/-- Total number of input accesses in a 2-register passive program. -/
def Pass2Prog.accesses : List Pass2Instr → Nat
  | [] => 0
  | .addOut _ :: rest => Pass2Prog.accesses rest
  | .addWorkConst _ :: rest => Pass2Prog.accesses rest
  | .addInputOut _ :: rest => 1 + Pass2Prog.accesses rest
  | .addInputWork _ :: rest => 1 + Pass2Prog.accesses rest

/-- Number of input accesses to the work register `R`. -/
def Pass2Prog.workAccesses : List Pass2Instr → Nat
  | [] => 0
  | .addInputWork _ :: rest => 1 + Pass2Prog.workAccesses rest
  | _ :: rest => Pass2Prog.workAccesses rest

theorem Pass2Prog.workAccesses_le_accesses (prog : List Pass2Instr) :
    Pass2Prog.workAccesses prog ≤ Pass2Prog.accesses prog := by
  induction prog with
  | nil => exact Nat.le_refl 0
  | cons i rest ih =>
    cases i <;> simp only [Pass2Prog.workAccesses, Pass2Prog.accesses] <;> omega

/--
Exact coefficient `[R^dR x^dx] (∑_k poly[k] * (R + b + a * x)^k)` in `ℕ` (reduced mod `p` during execution).
By the trinomial expansion `(R + a*x + b)^k = ∑_{d=0}^k C(k, d) b^{k-d} (R + a*x)^d`,
setting `d = dR + dx`, the coefficient of `R^dR * x^dx` is exactly
`(∑_k poly[k] * C(k, d) * b^{k - d}) * (C(d, dx) * a^{dx})`.
-/
def polyAtShiftCoeff (poly : List Nat) (b a dR dx : Nat) : Nat :=
  let d := dR + dx
  (sumNat poly.length (fun k => poly.getD k 0 * choose k d * b ^ (k - d))) * (choose d dx * a ^ dx)

/-- Formal symbolic state of a 2-register passive program in `𝔽_p[O, R, x]`. -/
structure State2 where
  /-- Constant part of the affine expression stored in the work register. -/
  b : Nat
  /-- Input coefficient of the affine expression stored in the work register. -/
  a : Nat
  /-- Coefficients of the increment polynomial in the initial work register and the input. -/
  coeff : Nat → Nat → Nat

/-- Execute a single `Pass2Instr` on the formal polynomial state in `𝔽_p[O, R, x]`. -/
def Pass2Instr.exec (p : Nat) (st : State2) : Pass2Instr → State2
  | .addOut poly =>
    { st with coeff := fun dR dx => (st.coeff dR dx + polyAtShiftCoeff poly st.b st.a dR dx) % p }
  | .addWorkConst c =>
    { st with b := (st.b + c) % p }
  | .addInputOut lam =>
    { st with coeff := fun dR dx => (st.coeff dR dx + if dR = 0 ∧ dx = 1 then lam else 0) % p }
  | .addInputWork lam =>
    { st with a := (st.a + lam) % p }

/-- Execute a `Pass2Prog` from a given state. -/
def Pass2Prog.execFrom (p : Nat) : List Pass2Instr → State2 → State2
  | [], st => st
  | i :: rest, st => Pass2Prog.execFrom p rest (i.exec p st)

/-- Execute a `Pass2Prog` from the clean initial state `R = R + 0 + 0*x`, `ΔO = 0`. -/
def Pass2Prog.exec (p : Nat) (prog : List Pass2Instr) : State2 :=
  Pass2Prog.execFrom p prog ⟨0, 0, fun _ _ => 0⟩

/--
Clean computation of univariate polynomial `f(x) = ∑_d f[d] x^d ∈ 𝔽_p[x]` in `𝔽_p[O, R, x]`:
  1. Work register `R` is restored identically (`b % p = 0 ∧ a % p = 0`), and
  2. Every formal monomial coefficient `[R^dR x^dx] ΔO` agrees mod `p` with `[x^dx] f`
     when `dR = 0` and `0` when `dR > 0`.
-/
def CleanlyComputes2 (p : Nat) (prog : List Pass2Instr) (f : List Nat) : Prop :=
  let st := Pass2Prog.exec p prog
  st.b % p = 0 ∧ st.a % p = 0 ∧
  ∀ dR dx : Nat, st.coeff dR dx % p = (if dR = 0 then f.getD dx 0 else 0) % p

/-- Membership `f ∈ RP^{pass}_{𝔽_p}(2, t)`: exists a passive 2-register program with `≤ t` accesses. -/
def InRPPass2 (p t : Nat) (f : List Nat) : Prop :=
  ∃ prog : List Pass2Instr, Pass2Prog.accesses prog ≤ t ∧ CleanlyComputes2 p prog f

/-- Helper: univariate monomial `x^d` as a coefficient list `[0, ..., 0, 1]`. -/
def monomial (d : Nat) : List Nat :=
  List.replicate d 0 ++ [1]

theorem monomial_getD (d k : Nat) : (monomial d).getD k 0 = if k = d then 1 else 0 := by
  unfold monomial
  by_cases hlt : k < d
  · have hne : k ≠ d := by omega
    simp only [hne, ↓reduceIte, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simp [hlt]), List.getElem?_replicate]
    simp [hlt]
  · by_cases heq : k = d
    · subst heq
      simp only [↓reduceIte, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by simp)]
      simp
    · have hgt : d < k := by omega
      simp only [heq, ↓reduceIte, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by simp; omega)]
      have hlen : [1].length ≤ k - (List.replicate d 0).length := by simp; omega
      rw [List.getElem?_eq_none hlen]
      rfl

/-! ## 2. Trace Extraction for Necessity (`⇒`) -/

/-- List of all `a`-values held by register `R` BEFORE each `addInputWork`, plus initial `a0`. -/
private def traceWorkA (p : Nat) : List Pass2Instr → Nat → List Nat
  | [], _ => []
  | .addInputWork lam :: rest, a => a :: traceWorkA p rest ((a + lam) % p)
  | _ :: rest, a => traceWorkA p rest a

/-- Weighted list of `(a, h)` contributions to total degree `d ≥ 2` across all `addOut` instructions. -/
private def degTerms (p d : Nat) : List Pass2Instr → Nat → Nat → List (Nat × Nat)
  | [], _, _ => []
  | .addOut poly :: rest, b, a =>
    let h := sumNat poly.length (fun k => poly.getD k 0 * choose k d * b ^ (k - d)) % p
    (a, h) :: degTerms p d rest b a
  | .addWorkConst c :: rest, b, a => degTerms p d rest ((b + c) % p) a
  | .addInputOut _ :: rest, b, a => degTerms p d rest b a
  | .addInputWork lam :: rest, b, a => degTerms p d rest b ((a + lam) % p)

/-- Evaluate `∑_{(a, h) ∈ L} h * a^j` over `Nat`. -/
private def evalPairsPow (L : List (Nat × Nat)) (j : Nat) : Nat :=
  match L with
  | [] => 0
  | (a, h) :: rest => h * a ^ j + evalPairsPow rest j

/-- Evaluate `∑_{(a, h) ∈ L} (h : Int) * f a` over `Int`. -/
private def evalPairsInt (L : List (Nat × Nat)) (f : Nat → Int) : Int :=
  match L with
  | [] => 0
  | (a, h) :: rest => (h : Int) * f a + evalPairsInt rest f

private theorem evalPairsInt_congr_mod {p : Nat} (L : List (Nat × Nat))
    {f g : Nat → Int} (hfg : ∀ a h, (a, h) ∈ L → f a % (p : Int) = g a % (p : Int)) :
    evalPairsInt L f % (p : Int) = evalPairsInt L g % (p : Int) := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨a, h⟩
    simp only [evalPairsInt]
    have h1 := hfg a h (List.mem_cons_self ..)
    have h2 := ih (fun a' h' hm => hfg a' h' (List.mem_cons_of_mem _ hm))
    rw [Int.add_emod, Int.mul_emod, h1, ← Int.mul_emod, h2, ← Int.add_emod]

private theorem evalPairsInt_zero {L : List (Nat × Nat)} {f : Nat → Int}
    (hf : ∀ a h, (a, h) ∈ L → f a = 0) : evalPairsInt L f = 0 := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨a, h⟩
    simp only [evalPairsInt, hf a h (List.mem_cons_self ..), Int.mul_zero, Int.zero_add]
    exact ih (fun a' h' hm => hf a' h' (List.mem_cons_of_mem _ hm))

private theorem evalPairsInt_sumInt (L : List (Nat × Nat)) (n : Nat) (F : Nat → Nat → Int) :
    evalPairsInt L (fun a => sumInt n (fun r => F r a)) =
      sumInt n (fun r => evalPairsInt L (fun a => F r a)) := by
  induction n with
  | zero =>
    simp only [sumInt]
    exact evalPairsInt_zero (fun _ _ _ => rfl)
  | succ m ih =>
    have hstep : ∀ a, sumInt (m + 1) (fun r => F r a) = sumInt m (fun r => F r a) + F m a :=
      fun _ => rfl
    have hadd : ∀ (g1 g2 : Nat → Int),
        evalPairsInt L (fun a => g1 a + g2 a) = evalPairsInt L g1 + evalPairsInt L g2 := by
      clear ih
      intro g1 g2
      induction L with
      | nil => rfl
      | cons hd tl iht =>
        rcases hd with ⟨a, h⟩
        simp only [evalPairsInt, Int.mul_add]
        rw [iht]
        omega
    simp only [hstep, hadd, ih, sumInt_succ]

private theorem evalPairsInt_const_mul (L : List (Nat × Nat)) (c : Int) (f : Nat → Int) :
    evalPairsInt L (fun a => c * f a) = c * evalPairsInt L f := by
  induction L with
  | nil => simp [evalPairsInt]
  | cons hd tl ih =>
    rcases hd with ⟨a, h⟩
    simp only [evalPairsInt, ih, Int.mul_add]
    congr 1
    rw [← Int.mul_assoc, Int.mul_comm (h : Int) c, Int.mul_assoc]

private theorem evalPairsInt_pow_eq (L : List (Nat × Nat)) (j : Nat) :
    evalPairsInt L (fun a => (a : Int) ^ j) = (evalPairsPow L j : Int) := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨a, h⟩
    simp only [evalPairsInt, evalPairsPow, ih, Int.natCast_add, Int.natCast_mul, Int.natCast_pow]

private theorem traceWorkA_length (p : Nat) (prog : List Pass2Instr) (a : Nat) :
    (traceWorkA p prog a).length = Pass2Prog.workAccesses prog := by
  induction prog generalizing a with
  | nil => rfl
  | cons i rest ih =>
    cases i <;> simp only [traceWorkA, Pass2Prog.workAccesses, List.length_cons, ih] <;> omega

private theorem degTerms_mem_traceWorkA (p d : Nat) (prog : List Pass2Instr) (b a : Nat)
    (hclosed : (Pass2Prog.execFrom p prog ⟨b, a, fun _ _ => 0⟩).a = a) :
    ∀ x h, (x, h) ∈ degTerms p d prog b a →
      x ∈ (if Pass2Prog.workAccesses prog = 0 then [a] else traceWorkA p prog a) := by
  have hmain : ∀ (pr : List Pass2Instr) (b0 a0 : Nat) (x h : Nat),
      (x, h) ∈ degTerms p d pr b0 a0 →
      x = (Pass2Prog.execFrom p pr ⟨b0, a0, fun _ _ => 0⟩).a ∨ x ∈ traceWorkA p pr a0 := by
    intro pr
    induction pr with
    | nil => intro b0 a0 x h hm; cases hm
    | cons instr rest ih =>
      intro b0 a0 x h hm
      cases instr with
      | addOut poly =>
        simp only [degTerms, List.mem_cons] at hm
        have hexec : (Pass2Prog.execFrom p (.addOut poly :: rest) ⟨b0, a0, fun _ _ => 0⟩).a =
            (Pass2Prog.execFrom p rest ⟨b0, a0, fun _ _ => 0⟩).a := by
          have ha_indep : ∀ (r : List Pass2Instr) (s1 s2 : State2),
              s1.a = s2.a → (Pass2Prog.execFrom p r s1).a = (Pass2Prog.execFrom p r s2).a := by
            intro r
            induction r with
            | nil => intro s1 s2 heq; exact heq
            | cons i2 r2 ih2 =>
              intro s1 s2 heq
              cases i2 <;> exact ih2 _ _ (by simp [Pass2Instr.exec, heq])
          exact ha_indep rest _ _ rfl
        rw [hexec]
        rcases hm with heq | hrest
        · rcases heq with ⟨rfl, rfl⟩
          clear ih hexec
          induction rest generalizing b0 a0 with
          | nil => left; rfl
          | cons i2 r2 ih2 =>
            cases i2 with
            | addInputWork lam => right; simp [traceWorkA]
            | addOut poly2 =>
              have hsame : (Pass2Prog.execFrom p (.addOut poly2 :: r2) ⟨b0, a0, fun _ _ => 0⟩).a =
                  (Pass2Prog.execFrom p r2 ⟨b0, a0, fun _ _ => 0⟩).a := by
                have ha_indep : ∀ (r : List Pass2Instr) (s1 s2 : State2),
                    s1.a = s2.a → (Pass2Prog.execFrom p r s1).a = (Pass2Prog.execFrom p r s2).a := by
                  intro r; induction r with
                  | nil => intro s1 s2 heq; exact heq
                  | cons i3 r3 ih3 =>
                    intro s1 s2 heq; cases i3 <;> exact ih3 _ _ (by simp [Pass2Instr.exec, heq])
                exact ha_indep r2 _ _ rfl
              rw [hsame]; exact ih2 b0 a0
            | addWorkConst c => exact ih2 ((b0 + c) % p) a0
            | addInputOut lam =>
              have hsame : (Pass2Prog.execFrom p (.addInputOut lam :: r2) ⟨b0, a0, fun _ _ => 0⟩).a =
                  (Pass2Prog.execFrom p r2 ⟨b0, a0, fun _ _ => 0⟩).a := by
                have ha_indep : ∀ (r : List Pass2Instr) (s1 s2 : State2),
                    s1.a = s2.a → (Pass2Prog.execFrom p r s1).a = (Pass2Prog.execFrom p r s2).a := by
                  intro r; induction r with
                  | nil => intro s1 s2 heq; exact heq
                  | cons i3 r3 ih3 =>
                    intro s1 s2 heq; cases i3 <;> exact ih3 _ _ (by simp [Pass2Instr.exec, heq])
                exact ha_indep r2 _ _ rfl
              rw [hsame]; exact ih2 b0 a0
        · exact ih b0 a0 x h hrest
      | addWorkConst c =>
        simp only [degTerms] at hm
        exact ih ((b0 + c) % p) a0 x h hm
      | addInputOut lam =>
        simp only [degTerms] at hm
        have hexec : (Pass2Prog.execFrom p (.addInputOut lam :: rest) ⟨b0, a0, fun _ _ => 0⟩).a =
            (Pass2Prog.execFrom p rest ⟨b0, a0, fun _ _ => 0⟩).a := by
          have ha_indep : ∀ (r : List Pass2Instr) (s1 s2 : State2),
              s1.a = s2.a → (Pass2Prog.execFrom p r s1).a = (Pass2Prog.execFrom p r s2).a := by
            intro r; induction r with
            | nil => intro s1 s2 heq; exact heq
            | cons i3 r3 ih3 =>
              intro s1 s2 heq; cases i3 <;> exact ih3 _ _ (by simp [Pass2Instr.exec, heq])
          exact ha_indep rest _ _ rfl
        rw [hexec]; exact ih b0 a0 x h hm
      | addInputWork lam =>
        simp only [degTerms] at hm
        simp only [Pass2Prog.execFrom, Pass2Instr.exec, traceWorkA, List.mem_cons]
        rcases ih b0 ((a0 + lam) % p) x h hm with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (Or.inr h2)
  intro x h hm
  have hres := hmain prog b a x h hm
  rw [hclosed] at hres
  by_cases hw : Pass2Prog.workAccesses prog = 0
  · simp only [hw, ↓reduceIte, List.mem_singleton]
    rcases hres with rfl | hmem
    · rfl
    · have hlen := traceWorkA_length p prog a
      rw [hw] at hlen
      cases ht : traceWorkA p prog a with
      | nil => rw [ht] at hmem; cases hmem
      | cons _ _ => rw [ht] at hlen; simp at hlen
  · simp only [hw, ↓reduceIte]
    rcases hres with rfl | hmem
    · clear hmain hm hclosed
      induction prog generalizing x with
      | nil => simp [Pass2Prog.workAccesses] at hw
      | cons instr rest ih =>
        cases instr with
        | addInputWork lam => simp [traceWorkA]
        | addOut _ => exact ih x hw
        | addWorkConst _ => exact ih x hw
        | addInputOut _ => exact ih x hw
    · exact hmem

/-- Exact degree-`d ≥ 2` coefficient identity relating `execFrom` to `degTerms`! -/
private theorem execFrom_coeff_eq_degTerms (p d j : Nat) (hd : 2 ≤ d) (hj : j ≤ d)
    (prog : List Pass2Instr) (st : State2) :
    (Pass2Prog.execFrom p prog st).coeff (d - j) j % p =
      (st.coeff (d - j) j + choose d j * evalPairsPow (degTerms p d prog st.b st.a) j) % p := by
  induction prog generalizing st with
  | nil => simp [Pass2Prog.execFrom, degTerms, evalPairsPow]
  | cons instr rest ih =>
    cases instr with
    | addOut poly =>
      simp only [Pass2Prog.execFrom, Pass2Instr.exec, degTerms, evalPairsPow]
      rw [ih]
      simp only [polyAtShiftCoeff]
      have hsum : d - j + j = d := by omega
      rw [hsum]
      let H := sumNat poly.length (fun k => poly.getD k 0 * choose k d * st.b ^ (k - d))
      let T := evalPairsPow (degTerms p d rest st.b st.a) j
      have hrearr :
          ((st.coeff (d - j) j + H * (choose d j * st.a ^ j)) % p + choose d j * T) % p =
          (st.coeff (d - j) j + choose d j * (H % p * st.a ^ j + T)) % p := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.mul_add, ← Nat.add_assoc]
        rw [Nat.add_mod (st.coeff (d - j) j + H * (choose d j * st.a ^ j)),
            Nat.add_mod (st.coeff (d - j) j + choose d j * (H % p * st.a ^ j))]
        congr 1
        congr 1
        rw [Nat.add_mod, Nat.add_mod (st.coeff (d - j) j)]
        congr 1
        congr 1
        have hcomm : H * (choose d j * st.a ^ j) = choose d j * (H * st.a ^ j) := by
          rw [← Nat.mul_assoc, Nat.mul_comm H (choose d j), Nat.mul_assoc]
        rw [hcomm]
        simp [Nat.mul_mod]
      exact hrearr
    | addWorkConst c =>
      simp only [Pass2Prog.execFrom, Pass2Instr.exec, degTerms]
      exact ih _
    | addInputOut lam =>
      simp only [Pass2Prog.execFrom, Pass2Instr.exec, degTerms]
      rw [ih]
      have hnot : ¬ (d - j = 0 ∧ j = 1) := by omega
      simp only [hnot, ↓reduceIte, Nat.add_zero]
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    | addInputWork lam =>
      simp only [Pass2Prog.execFrom, Pass2Instr.exec, degTerms]
      exact ih _

private theorem evalPairsPow_mod_eq_digitSum {p : Nat} (hp : IsPrime p)
    (L : List (Nat × Nat)) (n : Nat) :
    evalPairsPow L n % p = evalPairsPow L (digitSum p n) % p := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨a, h⟩
    simp only [evalPairsPow]
    rw [Nat.add_mod, Nat.mul_mod, pow_mod_eq_pow_digitSum hp a n, ← Nat.mul_mod, ih, ← Nat.add_mod]

/-! ## 3. Necessity (`⇒`) of Theorem T1 -/

theorem rp_pass_two_necessary {p t : Nat} (hp : IsPrime p) (ht : 1 ≤ t)
    (f : List Nat) (hmem : InRPPass2 p t f) :
    ∀ d : Nat, 2 ≤ d → f.getD d 0 % p ≠ 0 →
      digitSum p d ≤ min (p - 1) (t - 1) := by
  obtain ⟨prog, hacc, hb0, ha0, hclean⟩ := hmem
  intro d hd hfd
  let L := degTerms p d prog 0 0
  -- Step 1: For every j ≤ d, choose d j * evalPairsPow L j ≡ (if j = d then f[d] else 0) (mod p)
  have hcoeff : ∀ j ≤ d,
      (choose d j * evalPairsPow L j) % p = (if j = d then f.getD d 0 else 0) % p := by
    intro j hj
    have h1 := execFrom_coeff_eq_degTerms p d j hd hj prog ⟨0, 0, fun _ _ => 0⟩
    have h2 := hclean (d - j) j
    change (Pass2Prog.execFrom p prog ⟨0, 0, fun _ _ => 0⟩).coeff (d - j) j % p = _ at h2
    rw [h1, Nat.zero_add] at h2
    rw [h2]
    by_cases hjd : j = d
    · subst hjd; simp
    · have hsub : d - j ≠ 0 := by omega
      simp [hjd, hsub]
  -- Step 2: Top equation (j = d): evalPairsPow L d % p = f[d] % p ≠ 0!
  have htop : evalPairsPow L d % p = f.getD d 0 % p := by
    have h := hcoeff d (Nat.le_refl d)
    simp only [choose_self, Nat.one_mul, ↓reduceIte] at h
    exact h
  -- Step 3: For every r < digitSum p d, evalPairsPow L r % p = 0!
  have hvanish : ∀ r < digitSum p d, evalPairsPow L r % p = 0 := by
    intro r hr
    obtain ⟨j, hj_le, hj_sum, hj_ch, hj_lt⟩ := exists_lucas_sub hp d r (Nat.le_of_lt hr)
    have hj_strict : j < d := hj_lt hr
    have hne : j ≠ d := by omega
    have h0 := hcoeff j hj_le
    simp only [hne, ↓reduceIte, Nat.zero_mod] at h0
    have heval0 : evalPairsPow L j % p = 0 := by
      by_cases hz : evalPairsPow L j % p = 0
      · exact hz
      · exfalso; exact prime_mul_mod_ne_zero hp hj_ch hz h0
    rw [evalPairsPow_mod_eq_digitSum hp L j, hj_sum] at heval0
    exact heval0
  -- Claim 1: digitSum p d ≤ p - 1
  have hbound_p : digitSum p d ≤ p - 1 := by
    by_cases hle : digitSum p d ≤ p - 1
    · exact hle
    · exfalso
      have hge : p ≤ digitSum p d := by have := hp.1; omega
      let r := digitSum p d - (p - 1)
      have hr_pos : 1 ≤ r := by have := hp.1; omega
      have hr_lt : r < digitSum p d := by have := hp.1; omega
      have h0 : evalPairsPow L r % p = 0 := hvanish r hr_lt
      -- Show evalPairsPow L (digitSum p d) % p = evalPairsPow L r % p via Fermat (`a^p ≡ a`)!
      have heq_pow : ∀ a : Nat, a ^ (digitSum p d) % p = a ^ r % p := by
        intro a
        have hsplit : digitSum p d = (r - 1) + p := by omega
        have hr1 : r = (r - 1) + 1 := by omega
        rw [hsplit, Nat.pow_add, Nat.mul_mod, fermat_little hp, ← Nat.mul_mod]
        have hmul1 : a ^ (r - 1) * a = a ^ r := by
          conv => rhs; rw [hr1]
          rw [Nat.pow_succ]
        rw [hmul1]
      have heq_sum : ∀ M : List (Nat × Nat), evalPairsPow M (digitSum p d) % p = evalPairsPow M r % p := by
        intro M
        induction M with
        | nil => rfl
        | cons hd tl ihm =>
          rcases hd with ⟨a, h⟩
          simp only [evalPairsPow]
          rw [Nat.add_mod, Nat.mul_mod, heq_pow a, ← Nat.mul_mod, ihm, ← Nat.add_mod]
      have hcontra : f.getD d 0 % p = 0 := by
        rw [← htop, evalPairsPow_mod_eq_digitSum hp L d, heq_sum L, h0]
      exact hfd hcontra
  -- Claim 2: digitSum p d ≤ t - 1
  have hbound_t : digitSum p d ≤ t - 1 := by
    by_cases hle : digitSum p d ≤ t - 1
    · exact hle
    · exfalso
      let s := digitSum p d
      have hts : t ≤ s := by omega
      -- Collect the list A of visited shifts (`A.length = max 1 (workAccesses prog) ≤ t ≤ s`)
      let A := if Pass2Prog.workAccesses prog = 0 then [0] else traceWorkA p prog 0
      have hAlen : A.length ≤ s := by
        have hwa := Pass2Prog.workAccesses_le_accesses prog
        by_cases hw0 : Pass2Prog.workAccesses prog = 0
        · simp only [A, hw0, ↓reduceIte, List.length_singleton]; omega
        · simp only [A, hw0, ↓reduceIte, traceWorkA_length]; omega
      have hclosed : (Pass2Prog.execFrom p prog ⟨0, 0, fun _ _ => 0⟩).a = 0 := by
        -- Prove `execFrom.a < p` whenever initial `a < p`, so `a % p = 0` implies `a = 0`!
        have hltp : ∀ (pr : List Pass2Instr) (st : State2), st.a < p →
            (Pass2Prog.execFrom p pr st).a < p := by
          intro pr
          induction pr with
          | nil => intro st h; exact h
          | cons i r ihr =>
            intro st h
            cases i with
            | addInputWork lam => exact ihr _ (Nat.mod_lt _ hp.pos)
            | addOut _ => exact ihr _ h
            | addWorkConst _ => exact ihr _ h
            | addInputOut _ => exact ihr _ h
        have hlt := hltp prog ⟨0, 0, fun _ _ => 0⟩ hp.pos
        have hm0 : (Pass2Prog.execFrom p prog ⟨0, 0, fun _ _ => 0⟩).a % p = 0 := ha0
        rw [Nat.mod_eq_of_lt hlt] at hm0
        exact hm0
      have hmemA : ∀ x h, (x, h) ∈ L → x ∈ A :=
        degTerms_mem_traceWorkA p d prog 0 0 hclosed
      -- Consider P = prodLinear A (degree m = A.length ≤ s, monic, vanishes on every x ∈ A)
      let m := A.length
      let P := prodLinear A
      have hPlen : P.length = m + 1 := prodLinear_length A
      have hPlead : P.getD m 0 = 1 := prodLinear_lead A
      -- Evaluate `∑_{(a, h) ∈ L} h * a^(s - m) * evalIntPoly P a = 0`!
      have hzero_all : evalPairsInt L (fun a => (a : Int) ^ (s - m) * evalIntPoly P (a : Int)) = 0 := by
        apply evalPairsInt_zero
        intro a h hm
        rw [prodLinear_eval_mem A (hmemA a h hm), Int.mul_zero]
      -- Expand `a^(s - m) * evalIntPoly P a = sumInt (m + 1) (fun r => P[r] * a^(r + (s - m)))`
      have hexpand : evalPairsInt L (fun a => (a : Int) ^ (s - m) * evalIntPoly P (a : Int)) =
          sumInt (m + 1) (fun r => P.getD r 0 * evalPairsInt L (fun a => (a : Int) ^ (r + (s - m)))) := by
        have hfun : (fun a : Nat => (a : Int) ^ (s - m) * evalIntPoly P (a : Int)) =
            (fun a : Nat => sumInt (m + 1) (fun r => P.getD r 0 * (a : Int) ^ (r + (s - m)))) := by
          funext a
          rw [evalIntPoly_eq_sumInt, hPlen, ← sumInt_mul_left]
          apply sumInt_congr
          intro r _
          rw [Int.pow_add, ← Int.mul_assoc, Int.mul_comm ((a : Int) ^ (s - m)) (P.getD r 0),
              Int.mul_assoc, Int.mul_comm ((a : Int) ^ (s - m)) ((a : Int) ^ r)]
        rw [hfun, evalPairsInt_sumInt]
        apply sumInt_congr
        intro r _
        exact evalPairsInt_const_mul L (P.getD r 0) (fun a => (a : Int) ^ (r + (s - m)))
      rw [hexpand, sumInt_succ, hPlead, Int.one_mul] at hzero_all
      have hm_add : m + (s - m) = s := by omega
      rw [hm_add] at hzero_all
      -- Every lower term `r < m` has `r + (s - m) < s`, so its evalPairsInt is `0 mod p`!
      have hlow_mod : sumInt m (fun r => P.getD r 0 * evalPairsInt L (fun a => (a : Int) ^ (r + (s - m)))) % (p : Int) = 0 := by
        have hsumI_mod0 : ∀ (n : Nat) (g : Nat → Int),
            (∀ r < n, g r % (p : Int) = 0) → sumInt n g % (p : Int) = 0 := by
          intro n g hg
          induction n with
          | zero => simp [sumInt]
          | succ k ihk =>
            rw [sumInt_succ, Int.add_emod, ihk (fun r hr => hg r (by omega)),
                hg k (Nat.lt_succ_self k)]
            simp
        apply hsumI_mod0
        intro r hr
        rw [evalPairsInt_pow_eq, Int.mul_emod]
        have hv : evalPairsPow L (r + (s - m)) % p = 0 := hvanish (r + (s - m)) (by omega)
        have hvI : (evalPairsPow L (r + (s - m)) : Int) % (p : Int) = 0 := by
          rw [← Int.natCast_emod, hv]; rfl
        rw [hvI, Int.mul_zero, Int.zero_emod]
      have htop_mod0 : evalPairsInt L (fun a => (a : Int) ^ s) % (p : Int) = 0 := by
        have h0 : (sumInt m (fun r => P.getD r 0 * evalPairsInt L (fun a => (a : Int) ^ (r + (s - m)))) +
            evalPairsInt L (fun a => (a : Int) ^ s)) % (p : Int) = 0 := by
          rw [hzero_all]; simp
        rw [Int.add_emod, hlow_mod, Int.zero_add, Int.emod_emod] at h0
        exact h0
      rw [evalPairsInt_pow_eq] at htop_mod0
      have htop_nat0 : evalPairsPow L s % p = 0 := by
        have : ((evalPairsPow L s % p : Nat) : Int) = 0 := by
          rw [Int.natCast_emod]; exact htop_mod0
        omega
      have hcontra : f.getD d 0 % p = 0 := by
        rw [← htop, evalPairsPow_mod_eq_digitSum hp L d]
        exact htop_nat0
      exact hfd hcontra
  exact Nat.le_min.mpr ⟨hbound_p, hbound_t⟩

/-! ## 4. Sufficiency (`⇐`) of Theorem T1 via Forward Finite Differences -/

/-- Exact finite-difference weight `h_{s, a} ∈ {0..p-1}` satisfying
`∑_{a=0}^s h_{s, a} * a^r ≡ (if r = s then 1 else 0) (mod p)` for `s < p` and `r ≤ s`. -/
private noncomputable def fdWeight (p s a : Nat) (invFactS : Nat) : Nat :=
  if a ≤ s then
    let numI : Int := (invFactS : Int) * (altSign (s - a) * (choose s a : Int))
    (numI % (p : Int)).toNat
  else 0

private theorem fdWeight_sum_pow {p s r invFactS : Nat} (hp : IsPrime p)
    (_hs : s < p) (hr : r ≤ s) (hinv : (invFactS * fact s) % p = 1) :
    sumNat (s + 1) (fun a => fdWeight p s a invFactS * a ^ r) % p =
      if r = s then 1 else 0 := by
  have hp_pos : (0 : Int) < (p : Int) := by have := hp.pos; omega
  have hcast : ∀ a ≤ s,
      ((fdWeight p s a invFactS : Int)) % (p : Int) =
        ((invFactS : Int) * (altSign (s - a) * (choose s a : Int))) % (p : Int) := by
    intro a ha
    unfold fdWeight
    simp only [ha, ↓reduceIte]
    have hnn : 0 ≤ ((invFactS : Int) * (altSign (s - a) * (choose s a : Int))) % (p : Int) :=
      Int.emod_nonneg _ (by omega)
    rw [Int.toNat_of_nonneg hnn, Int.emod_emod]
  have hsum_eq :
      ((sumNat (s + 1) (fun a => fdWeight p s a invFactS * a ^ r) : Nat) : Int) % (p : Int) =
      ((invFactS : Int) * iterDiff s (fun y => (y : Int) ^ r) 0) % (p : Int) := by
    rw [iterDiff_eq_sum, ← sumInt_mul_left]
    have hnat_to_int : ∀ (n : Nat) (g : Nat → Nat),
        (sumNat n g : Int) = sumInt n (fun i => (g i : Int)) := by
      intro n g
      induction n with
      | zero => rfl
      | succ m ih => rw [sumNat_succ, sumInt_succ, Int.natCast_add, ih]
    rw [hnat_to_int]
    have hsumI_congr_mod : ∀ (n : Nat) (g1 g2 : Nat → Int),
        (∀ i < n, g1 i % (p : Int) = g2 i % (p : Int)) →
        sumInt n g1 % (p : Int) = sumInt n g2 % (p : Int) := by
      intro n g1 g2 hg
      induction n with
      | zero => rfl
      | succ m ih =>
        rw [sumInt_succ, sumInt_succ, Int.add_emod, ih (fun i hi => hg i (by omega)),
            hg m (Nat.lt_succ_self m), ← Int.add_emod]
    apply hsumI_congr_mod
    intro a ha
    have hale : a ≤ s := by omega
    rw [Int.natCast_mul, Int.natCast_pow, Int.mul_emod, hcast a hale, ← Int.mul_emod]
    have h0a : (0 + a : Nat) = a := Nat.zero_add a
    rw [h0a, Int.mul_assoc]
  have hval : ((invFactS : Int) * iterDiff s (fun y => (y : Int) ^ r) 0) % (p : Int) =
      if r = s then 1 else 0 := by
    by_cases hrs : r = s
    · simp only [hrs, ↓reduceIte]
      rw [(iterDiff_pow s s 0).2 rfl]
      rw [← Int.natCast_mul, ← Int.natCast_emod, hinv]
      rfl
    · simp only [hrs, ↓reduceIte]
      rw [(iterDiff_pow r s 0).1 (by omega), Int.mul_zero, Int.zero_emod]
  rw [hval] at hsum_eq
  rw [← Int.natCast_emod] at hsum_eq
  by_cases hrs : r = s
  · simp only [hrs, ↓reduceIte] at hsum_eq ⊢; omega
  · simp only [hrs, ↓reduceIte] at hsum_eq ⊢; omega

private def buildShiftSteps (polyAt : Nat → List Nat) : Nat → List Pass2Instr
  | 0 => [.addOut (polyAt 0)]
  | k + 1 => buildShiftSteps polyAt k ++ [.addInputWork 1, .addOut (polyAt (k + 1))]

private def buildSufficientProg (p M : Nat) (polyAt : Nat → List Nat) : List Pass2Instr :=
  buildShiftSteps polyAt M ++ [.addInputWork ((p - M % p) % p)]

private theorem Pass2Prog.accesses_append (p1 p2 : List Pass2Instr) :
    Pass2Prog.accesses (p1 ++ p2) = Pass2Prog.accesses p1 + Pass2Prog.accesses p2 := by
  induction p1 with
  | nil => simp [Pass2Prog.accesses]
  | cons i rest ih => cases i <;> simp [Pass2Prog.accesses, ih, Nat.add_assoc]

private theorem Pass2Prog.execFrom_append (p : Nat) (p1 p2 : List Pass2Instr) (st : State2) :
    Pass2Prog.execFrom p (p1 ++ p2) st = Pass2Prog.execFrom p p2 (Pass2Prog.execFrom p p1 st) := by
  induction p1 generalizing st with
  | nil => rfl
  | cons i rest ih => exact ih _

private theorem buildShiftSteps_accesses (polyAt : Nat → List Nat) (k : Nat) :
    Pass2Prog.accesses (buildShiftSteps polyAt k) = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [buildShiftSteps, Pass2Prog.accesses_append, Pass2Prog.accesses, ih]

private theorem buildShiftSteps_exec (p : Nat) (_hp : 0 < p) (polyAt : Nat → List Nat) (k : Nat) (hk : k < p) :
    let st := Pass2Prog.execFrom p (buildShiftSteps polyAt k) ⟨0, 0, fun _ _ => 0⟩
    st.b = 0 ∧ st.a = k ∧
    ∀ dR dx : Nat,
      st.coeff dR dx % p =
        sumNat (k + 1) (fun a => (polyAt a).getD (dR + dx) 0 * (choose (dR + dx) dx * a ^ dx)) % p := by
  induction k with
  | zero =>
    refine ⟨rfl, rfl, ?_⟩
    intro dR dx
    simp only [buildShiftSteps, Pass2Prog.execFrom, Pass2Instr.exec, Nat.zero_add, Nat.mod_mod,
      polyAtShiftCoeff, sumNat]
    -- At `b = 0`, `0 ^ (j - d)` is 1 iff `j = d` (for `j ≥ d`), else 0!
    have hsingle : sumNat (polyAt 0).length
        (fun j => (polyAt 0).getD j 0 * choose j (dR + dx) * 0 ^ (j - (dR + dx))) =
        (polyAt 0).getD (dR + dx) 0 := by
      by_cases hlt : dR + dx < (polyAt 0).length
      · rw [sumNat_single (k := dR + dx) hlt]
        · simp [choose_self]
        · intro j hj hne
          by_cases hjd : j < dR + dx
          · simp [choose_eq_zero_of_lt hjd]
          · have hpos : 0 < j - (dR + dx) := by omega
            simp [Nat.zero_pow hpos]
      · rw [sumNat_zero]
        · simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by omega)]; rfl
        · intro j hj
          have hjd : j < dR + dx := by omega
          simp [choose_eq_zero_of_lt hjd]
    rw [hsingle]
  | succ k ih =>
    obtain ⟨hb, ha, hcoeff⟩ := ih (by omega)
    simp only [buildShiftSteps, Pass2Prog.execFrom_append]
    let stK := Pass2Prog.execFrom p (buildShiftSteps polyAt k) ⟨0, 0, fun _ _ => 0⟩
    have ha1 : (stK.a + 1) % p = k + 1 := by
      rw [ha]; exact Nat.mod_eq_of_lt hk
    refine ⟨hb, ha1, ?_⟩
    intro dR dx
    simp only [Pass2Prog.execFrom, Pass2Instr.exec, hb, Nat.mod_mod, polyAtShiftCoeff]
    have ha_eq : ((Pass2Prog.execFrom p (buildShiftSteps polyAt k) ⟨0, 0, fun _ _ => 0⟩).a + 1) % p = k + 1 := ha1
    rw [ha_eq]
    have hsingle : sumNat (polyAt (k + 1)).length
        (fun j => (polyAt (k + 1)).getD j 0 * choose j (dR + dx) * 0 ^ (j - (dR + dx))) =
        (polyAt (k + 1)).getD (dR + dx) 0 := by
      by_cases hlt : dR + dx < (polyAt (k + 1)).length
      · rw [sumNat_single (k := dR + dx) hlt]
        · simp [choose_self]
        · intro j hj hne
          by_cases hjd : j < dR + dx
          · simp [choose_eq_zero_of_lt hjd]
          · have hpos : 0 < j - (dR + dx) := by omega
            simp [Nat.zero_pow hpos]
      · rw [sumNat_zero]
        · simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by omega)]; rfl
        · intro j hj
          have hjd : j < dR + dx := by omega
          simp [choose_eq_zero_of_lt hjd]
    rw [hsingle, Nat.add_mod, hcoeff dR dx, ← Nat.add_mod, sumNat_succ (k + 1)]

private theorem rp_pass_two_sufficient_one {p : Nat} (hp : IsPrime p) (f : List Nat)
    (hsuff : ∀ d : Nat, 2 ≤ d → f.getD d 0 % p ≠ 0 → digitSum p d ≤ min (p - 1) (1 - 1)) :
    InRPPass2 p 1 f := by
  refine ⟨[.addOut [f.getD 0 0], .addInputOut (f.getD 1 0)], Nat.le_refl 1, ?_⟩
  refine ⟨rfl, rfl, ?_⟩
  intro dR dx
  simp only [Pass2Prog.exec, Pass2Prog.execFrom, Pass2Instr.exec, Nat.zero_add, Nat.mod_mod,
    polyAtShiftCoeff, List.length_singleton, sumNat]
  by_cases h0 : dR = 0 ∧ dx = 0
  · rcases h0 with ⟨rfl, rfl⟩
    simp [choose]
  · by_cases h1 : dR = 0 ∧ dx = 1
    · rcases h1 with ⟨rfl, rfl⟩
      simp [choose]
    · have hgt0 : 0 < dR + dx := by omega
      have hch0 : choose 0 (dR + dx) = 0 := choose_eq_zero_of_lt hgt0
      simp only [h1, ↓reduceIte, hch0, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
      by_cases hdR0 : dR = 0
      · subst hdR0
        have hdx2 : 2 ≤ dx := by omega
        by_cases hfd : f.getD dx 0 % p = 0
        · simp only [↓reduceIte, hfd, Nat.zero_mod]
        · exfalso
          have hle := hsuff dx hdx2 hfd
          have h0s : digitSum p dx = 0 := by omega
          have := (digitSum_eq_zero_iff hp.1 dx).mp h0s
          omega
      · simp [hdR0]

theorem rp_pass_two_sufficient {p t : Nat} (hp : IsPrime p) (ht : 1 ≤ t)
    (f : List Nat)
    (hsuff : ∀ d : Nat, 2 ≤ d → f.getD d 0 % p ≠ 0 → digitSum p d ≤ min (p - 1) (t - 1)) :
    InRPPass2 p t f := by
  by_cases ht1 : t = 1
  · subst t
    exact rp_pass_two_sufficient_one hp f hsuff
  · -- When `t ≥ 2`: `M = min (p - 1) (t - 1) ≥ 1`, visit `a = 0, 1, ..., M` in `M + 1 ≤ t` accesses!
    let M := min (p - 1) (t - 1)
    have hM_ge1 : 1 ≤ M := by have := hp.1; omega
    have hM_lt_p : M < p := by have := hp.1; omega
    have hM_le_t : M + 1 ≤ t := by omega
    -- Choose modular inverses of `fact s` for all `s < p` (classical choice, standard Lean axiom!)
    have hinv_ex : ∀ s : Nat, ∃ u : Nat, s < p → (u * fact s) % p = 1 := by
      intro s
      by_cases hs : s < p
      · have hnd : fact s % p ≠ 0 := fun h => prime_not_dvd_fact hp s hs (Nat.dvd_of_mod_eq_zero h)
        obtain ⟨u, _, hu⟩ := exists_mod_inv hp hnd
        exact ⟨u, fun _ => hu⟩
      · exact ⟨0, fun h => absurd h hs⟩
    let invF : Nat → Nat := fun s => Classical.choose (hinv_ex s)
    have hinvF : ∀ s < p, (invF s * fact s) % p = 1 :=
      fun s hs => Classical.choose_spec (hinv_ex s) hs
    let fdW : Nat → Nat → Nat := fun s a => fdWeight p s a (invF s)
    let polyAt : Nat → List Nat := fun a =>
      List.ofFn fun (k : Fin f.length) =>
        if k.val = 0 then
          if a = 0 then f.getD 0 0 % p else 0
        else
          let c := f.getD k.val 0 % p
          if c = 0 then 0
          else
            let s := digitSum p k.val
            if s ≤ M then (c * fdW s a) % p else 0
    let prog := buildSufficientProg p M polyAt
    refine ⟨prog, ?_, ?_⟩
    · simp only [prog, buildSufficientProg, Pass2Prog.accesses_append, buildShiftSteps_accesses,
        Pass2Prog.accesses, Nat.add_zero]
      omega
    · simp only [CleanlyComputes2, prog, buildSufficientProg, Pass2Prog.exec,
        Pass2Prog.execFrom_append]
      obtain ⟨hb, ha, hcoeff⟩ := buildShiftSteps_exec p hp.pos polyAt M hM_lt_p
      simp only [Pass2Prog.execFrom, Pass2Instr.exec, hb, ha]
      refine ⟨Nat.zero_mod p, ?_, ?_⟩
      · rw [Nat.mod_eq_of_lt hM_lt_p, Nat.mod_mod]
        have hsub : M + (p - M) % p = p := by
          have : p - M < p := by omega
          rw [Nat.mod_eq_of_lt this]; omega
        rw [hsub, Nat.mod_self]
      · intro dR dx
        rw [hcoeff dR dx]
        let d := dR + dx
        have hget : ∀ a : Nat, (polyAt a).getD d 0 =
            if d < f.length then
              if d = 0 then (if a = 0 then f.getD 0 0 % p else 0)
              else
                let c := f.getD d 0 % p
                if c = 0 then 0
                else if digitSum p d ≤ M then (c * fdW (digitSum p d) a) % p else 0
            else 0 := by
          intro a
          simp only [polyAt, List.getD_eq_getElem?_getD]
          by_cases hdlt : d < f.length
          · simp only [hdlt, ↓reduceIte, List.getElem?_ofFn]
            simp [hdlt]
          · simp only [hdlt, ↓reduceIte]
            rw [List.getElem?_eq_none (by simp; omega)]; rfl
        by_cases hdlt : d < f.length
        · by_cases hd0 : d = 0
          · have hdR0 : dR = 0 := by omega
            have hdx0 : dx = 0 := by omega
            subst hdR0; subst hdx0
            simp only [↓reduceIte]
            have hsing : sumNat (M + 1) (fun a => (polyAt a).getD 0 0 * (choose 0 0 * a ^ 0)) =
                f.getD 0 0 % p := by
              rw [sumNat_single (k := 0) (Nat.succ_pos M)]
              · have h0 := hget 0
                change (polyAt 0).getD 0 0 * (choose 0 0 * 0 ^ 0) = f.getD 0 0 % p
                have hdlt0 : 0 < f.length := hdlt
                simp only [d, Nat.zero_add, hdlt0, ↓reduceIte] at h0
                rw [h0]; simp [choose]
              · intro a _ hne
                have ha0 := hget a
                have hdlt0 : 0 < f.length := hdlt
                simp only [d, Nat.zero_add, hdlt0, hne, ↓reduceIte] at ha0
                change (polyAt a).getD 0 0 * (choose 0 0 * a ^ 0) = 0
                rw [ha0]; simp
            rw [hsing, Nat.mod_mod]
          · let c := f.getD d 0 % p
            by_cases hc0 : c = 0
            · have hz : sumNat (M + 1) (fun a => (polyAt a).getD d 0 * (choose d dx * a ^ dx)) = 0 := by
                apply sumNat_zero
                intro a _
                rw [hget a]
                simp only [hdlt, hd0, ↓reduceIte]
                change (if c = 0 then 0 else if digitSum p d ≤ M then c * fdW (digitSum p d) a % p else 0) *
                    (choose d dx * a ^ dx) = 0
                simp only [hc0, ↓reduceIte, Nat.zero_mul]
              rw [hz, Nat.zero_mod]
              by_cases hdR0 : dR = 0
              · subst hdR0
                have hdeq : dx = d := by omega
                rw [hdeq]; exact hc0.symm
              · simp [hdR0]
            · let s := digitSum p d
              have hs_le_M : s ≤ M := by
                by_cases hd1 : d = 1
                · have hs1 : s = 1 := by
                    change digitSum p d = 1
                    rw [hd1]; exact digitSum_of_lt hp.1 hp.gt_one
                  omega
                · exact hsuff d (by omega) hc0
              have hs_lt_p : s < p := by omega
              have hcongr :
                  sumNat (M + 1) (fun a => (polyAt a).getD d 0 * (choose d dx * a ^ dx)) % p =
                  (c * choose d dx * sumNat (s + 1) (fun a => fdW s a * a ^ dx)) % p := by
                have h1 :
                    sumNat (M + 1) (fun a => (polyAt a).getD d 0 * (choose d dx * a ^ dx)) % p =
                    sumNat (M + 1) (fun a => c * choose d dx * (fdW s a * a ^ dx)) % p := by
                  apply sumNat_congr_mod
                  intro a _
                  rw [hget a]
                  simp only [hdlt, hd0, c, hc0, s, hs_le_M, ↓reduceIte]
                  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
                  congr 1
                  calc
                    c * fdW s a * (choose d dx * a ^ dx)
                        = c * (fdW s a * (choose d dx * a ^ dx)) := Nat.mul_assoc _ _ _
                    _   = c * (choose d dx * (fdW s a * a ^ dx)) := by
                          rw [← Nat.mul_assoc (fdW s a), Nat.mul_comm (fdW s a) (choose d dx),
                              Nat.mul_assoc]
                    _   = c * choose d dx * (fdW s a * a ^ dx) := (Nat.mul_assoc _ _ _).symm
                rw [h1, sumNat_mul_left]
                have htrunc : ∀ (k : Nat), s ≤ k →
                    sumNat (k + 1) (fun a => fdW s a * a ^ dx) =
                    sumNat (s + 1) (fun a => fdW s a * a ^ dx) := by
                  intro k hk
                  induction k with
                  | zero =>
                    have hs0 : s = 0 := by omega
                    rw [hs0]
                  | succ k' ihk =>
                    by_cases hsk : s = k' + 1
                    · rw [hsk]
                    · rw [sumNat_succ, ihk (by omega)]
                      have hgt : ¬ (k' + 1 ≤ s) := by omega
                      simp [fdW, fdWeight, hgt]
                rw [htrunc M hs_le_M]
              rw [hcongr]
              by_cases hch0 : choose d dx % p = 0
              · have hne : dx ≠ d := by
                  intro heq
                  have hch1 : choose d dx = 1 := by rw [heq, choose_self]
                  rw [hch1, Nat.mod_eq_of_lt hp.gt_one] at hch0
                  exact Nat.one_ne_zero hch0
                have hdRne : dR ≠ 0 := by omega
                simp only [hdRne, ↓reduceIte, Nat.zero_mod]
                rw [Nat.mul_mod, Nat.mul_mod c, hch0, Nat.mul_zero, Nat.zero_mod, Nat.zero_mul, Nat.zero_mod]
              · obtain ⟨hds_le, hds_lt⟩ := digitSum_le_of_choose_ne_zero hp d dx hch0
                have hsum_ferm :
                    sumNat (s + 1) (fun a => fdW s a * a ^ dx) % p =
                    sumNat (s + 1) (fun a => fdW s a * a ^ (digitSum p dx)) % p := by
                  apply sumNat_congr_mod
                  intro a _
                  rw [Nat.mul_mod, pow_mod_eq_pow_digitSum hp a dx, ← Nat.mul_mod]
                rw [Nat.mul_mod, hsum_ferm,
                    fdWeight_sum_pow hp hs_lt_p hds_le (hinvF s hs_lt_p)]
                by_cases hdR0 : dR = 0
                · subst hdR0
                  have hdeq : dx = d := by omega
                  simp only [hdeq, s, ↓reduceIte, choose_self, Nat.mul_one, c, Nat.mod_mod]
                · have hdx_lt : dx < d := by omega
                  have hstrict : digitSum p dx < s := hds_lt hdx_lt
                  have hne_s : digitSum p dx ≠ s := by omega
                  simp only [hdR0, hne_s, ↓reduceIte, Nat.mul_zero, Nat.zero_mod]
        · -- `d ≥ f.length`: both `polyAt` and `f` are `0` at index `d`!
          have hz : sumNat (M + 1) (fun a => (polyAt a).getD d 0 * (choose d dx * a ^ dx)) = 0 := by
            apply sumNat_zero
            intro a _
            rw [hget a]
            simp [hdlt]
          rw [hz, Nat.zero_mod]
          by_cases hdR0 : dR = 0
          · subst hdR0
            have hlen : f.length ≤ dx := by omega
            simp only [↓reduceIte, List.getD_eq_getElem?_getD]
            rw [List.getElem?_eq_none hlen]; simp
          · simp [hdR0]

/-! ## 5. Main Theorem T1 and Four Sharp Corollaries -/

/--
**Theorem T1 (Complete Base-`p` Digit-Sum Characterization of `RP^{pass}_{𝔽_p}(2, t)`).**
For every prime `p`, every input-access budget `t ≥ 1`, and every univariate polynomial
`f ∈ 𝔽_p[x]`:
  `f ∈ RP^{pass}_{𝔽_p}(2, t)  ↔  ∀ d ≥ 2, ([x^d] f ≠ 0 mod p) → s_p(d) ≤ min (p - 1) (t - 1)`.
-/
theorem rp_pass_two_iff (p t : Nat) (hp : IsPrime p) (ht : 1 ≤ t) (f : List Nat) :
    InRPPass2 p t f ↔
      ∀ d : Nat, 2 ≤ d → f.getD d 0 % p ≠ 0 →
        digitSum p d ≤ min (p - 1) (t - 1) :=
  ⟨rp_pass_two_necessary hp ht f, rp_pass_two_sufficient hp ht f⟩

/-- **Corollary T1a (Unbounded-Degree 2-Access Collapse in Characteristic `p`):**
For EVERY prime `p` and EVERY `m : Nat`, `x^(p^m) ∈ RP^{pass}_{𝔽_p}(2, 2)`.
Thus `D^{pass}_{2, 𝔽_p}(2) = +∞`, collapsing Vinciguerra's Theorems 3.2, 3.3, and 3.5! -/
theorem char_p_two_access_unbounded_degree (p m : Nat) (hp : IsPrime p) :
    InRPPass2 p 2 (monomial (p ^ m)) := by
  rw [rp_pass_two_iff p 2 hp (by decide)]
  intro d _ hne
  rw [monomial_getD] at hne
  by_cases hdm : d = p ^ m
  · subst hdm
    rw [digitSum_pow hp.1 m]
    have := hp.1; omega
  · simp [hdm] at hne

/-- **Corollary T1b (Exact `𝔽_2` Saturation — `x^3` is Uncomputable in 2 Registers for ALL `t`):**
Over `𝔽_2`, `x^3 ∉ RP^{pass}_{𝔽_2}(2, t)` for EVERY `t : Nat`! -/
theorem char_2_two_reg_x3_impossible (t : Nat) : ¬ InRPPass2 2 t (monomial 3) := by
  intro hmem
  have hs3 : digitSum 2 3 = 2 := by
    rw [digitSum_eq (by decide) 3 (by decide)]
    have h1 : digitSum 2 1 = 1 := digitSum_of_lt (by decide) (by decide)
    change 1 + digitSum 2 1 = 2
    rw [h1]
  have hne : (monomial 3).getD 3 0 % 2 ≠ 0 := by decide
  cases t with
  | zero =>
    obtain ⟨prog, hacc, hcl⟩ := hmem
    have h1 : InRPPass2 2 1 (monomial 3) := ⟨prog, Nat.le_trans hacc (by decide), hcl⟩
    have hle := (rp_pass_two_iff 2 1 IsPrime.two (by decide) (monomial 3)).mp h1 3 (by decide) hne
    rw [hs3] at hle; omega
  | succ t' =>
    have hle := (rp_pass_two_iff 2 (t' + 1) IsPrime.two (Nat.succ_pos t') (monomial 3)).mp hmem 3 (by decide) hne
    rw [hs3] at hle; omega

/-- **Corollary T1c (Exact Prime-Field Impossibility Threshold):**
If `s_p(d) ≥ p` and `d ≥ 2`, then `x^d ∉ RP^{pass}_{𝔽_p}(2, t)` for EVERY `t ≥ 1`! -/
theorem char_p_impossibility_threshold (p d t : Nat) (hp : IsPrime p) (hd : 2 ≤ d) (ht : 1 ≤ t)
    (hs : p ≤ digitSum p d) : ¬ InRPPass2 p t (monomial d) := by
  intro hmem
  have hne : (monomial d).getD d 0 % p ≠ 0 := by
    rw [monomial_getD]; simp; have := hp.gt_one; omega
  have hle := (rp_pass_two_iff p t hp ht (monomial d)).mp hmem d hd hne
  have := hp.1; omega

/-- **Corollary T1d (Characteristic-0 Limit Recovering Vinciguerra Theorem 3.5):**
Whenever `2 ≤ d < p`, `x^d ∈ RP^{pass}_{𝔽_p}(2, t) ↔ d + 1 ≤ t`! -/
theorem char_p_large_recovers_vinciguerra_thm35 (p d t : Nat) (hp : IsPrime p)
    (hd2 : 2 ≤ d) (hdp : d < p) (ht : 1 ≤ t) :
    InRPPass2 p t (monomial d) ↔ d + 1 ≤ t := by
  rw [rp_pass_two_iff p t hp ht (monomial d)]
  constructor
  · intro h
    have hne : (monomial d).getD d 0 % p ≠ 0 := by
      rw [monomial_getD]; simp; have := hp.gt_one; omega
    have hle := h d hd2 hne
    rw [digitSum_of_lt hp.1 hdp] at hle
    omega
  · intro hdt k hk hne
    rw [monomial_getD] at hne
    by_cases hkd : k = d
    · subst hkd
      rw [digitSum_of_lt hp.1 hdp]
      omega
    · simp [hkd] at hne

end

end Catalytic
