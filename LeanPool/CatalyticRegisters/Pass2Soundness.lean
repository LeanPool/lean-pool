/-
Copyright (c) 2026 Alexander S. Donahue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander S. Donahue
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.CatalyticRegisters.CommRing
public import LeanPool.CatalyticRegisters.PrimeFieldTools
public import LeanPool.CatalyticRegisters.DigitSumDichotomy
public import LeanPool.CatalyticRegisters.ExtensionFieldSeparation

/-!
# Literal Commutative-Ring Soundness Bridge for `T1` and `T1e`

In `Catalytic.DigitSumDichotomy` and `Catalytic.ExtensionFieldSeparation`, passive 2-register
programs (`Pass2Instr` over `𝔽_p` and `Pass2GF4Instr` over `𝔽_4`) are executed symbolically on
formal coefficient tables via `polyAtShiftCoeff` and `polyAtShiftCoeffGF4`.

To eliminate any formal-definition trust-base gap between symbolic binomial-coefficient execution
and literal ring evaluation, this module:
  1. Proves the **binomial theorem** `CRing.add_pow` from first principles over every commutative
     ring `R` (`[CRing R]`) with zero Mathlib dependencies.
  2. Defines direct literal ring execution `Pass2Prog.execRing` (literally `O ← O + evalPolyR poly r`,
     `r ← r + natCast c`, `O ← O + natCast lam * x`, `r ← r + natCast lam * x`) with NO binomial
     coefficients anywhere in its definition.
  3. Proves **Theorem `T1s_Pass2RingSoundness`**: for EVERY program `prog`, EVERY prime/modulus `p`,
     and EVERY commutative ring `R` of characteristic `p` (`(CRing.natCast p : R) = 0`), literal
     ring execution agrees identically with symbolic `Pass2Prog.exec` — and in particular,
     `CleanlyComputes2 p prog f` implies literal clean execution
     `Pass2Prog.execRing x prog (o, u) = (o + evalPolyR f x, u)` for all `o, u, x : R`.
  4. Defines direct literal execution `Pass2GF4Prog.execAlg` over ANY commutative `GF4`-algebra `R`
     (via any ring homomorphism `φ : GF4 → R`, including `R = GF4` with `φ = id`) and proves
     **Theorem `T1es_Pass2GF4Soundness`**: literal `GF4`-algebra execution agrees identically with
     symbolic `Pass2GF4Prog.exec`, and `CleanlyComputes2GF4 prog f` implies
     `Pass2GF4Prog.execAlg φ x prog (o, u) = (o + evalPolyGF4Alg φ f x, u)` for all `o, u, x : R`.
-/

namespace Catalytic

@[expose] public section

universe u

/-! ## 1. Finite Ring Sums and the Zero-Mathlib Binomial Theorem -/

/-- Finite sum `f 0 + f 1 + ... + f (n - 1)` in an arbitrary commutative ring `R`. -/
def sumR {R : Type u} [CRing R] : Nat → (Nat → R) → R
  | 0, _     => 0
  | n + 1, f => sumR n f + f n

section RingSums

variable {R : Type u} [CRing R]

@[simp] theorem sumR_zero (f : Nat → R) : sumR 0 f = 0 := rfl

theorem sumR_succ (n : Nat) (f : Nat → R) : sumR (n + 1) f = sumR n f + f n := rfl

theorem sumR_congr {n : Nat} {f g : Nat → R} (h : ∀ i < n, f i = g i) :
    sumR n f = sumR n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumR_succ, sumR_succ, ih (fun i hi => h i (by omega)), h m (Nat.lt_succ_self m)]

theorem sumR_eq_zero {n : Nat} {f : Nat → R} (h : ∀ i < n, f i = 0) :
    sumR n f = 0 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumR_succ, ih (fun i hi => h i (by omega)), h m (Nat.lt_succ_self m), CRing.add_zero]

theorem sumR_add (n : Nat) (f g : Nat → R) :
    sumR n (fun i => f i + g i) = sumR n f + sumR n g := by
  induction n with
  | zero => simp [sumR]
  | succ m ih =>
    rw [sumR_succ, sumR_succ, sumR_succ, ih]
    calc
      (sumR m f + sumR m g) + (f m + g m)
          = sumR m f + (sumR m g + (f m + g m)) := CRing.add_assoc _ _ _
      _   = sumR m f + ((sumR m g + f m) + g m) := by rw [← CRing.add_assoc (sumR m g)]
      _   = sumR m f + ((f m + sumR m g) + g m) := by rw [CRing.add_comm (sumR m g) (f m)]
      _   = sumR m f + (f m + (sumR m g + g m)) := by rw [CRing.add_assoc (f m)]
      _   = (sumR m f + f m) + (sumR m g + g m) := (CRing.add_assoc _ _ _).symm

theorem sumR_mul_left (n : Nat) (c : R) (f : Nat → R) :
    sumR n (fun i => c * f i) = c * sumR n f := by
  induction n with
  | zero => simp [sumR]
  | succ m ih =>
    rw [sumR_succ, sumR_succ, ih, CRing.left_distrib]

theorem sumR_mul_right (n : Nat) (f : Nat → R) (c : R) :
    sumR n (fun i => f i * c) = sumR n f * c := by
  induction n with
  | zero => simp [sumR]
  | succ m ih =>
    rw [sumR_succ, sumR_succ, ih, CRing.right_distrib]

theorem sumR_swap (m n : Nat) (f : Nat → Nat → R) :
    sumR m (fun i => sumR n (fun j => f i j)) =
      sumR n (fun j => sumR m (fun i => f i j)) := by
  induction m with
  | zero =>
    symm
    exact sumR_eq_zero (fun _ _ => rfl)
  | succ m' ih =>
    rw [sumR_succ, ih]
    symm
    exact sumR_add n (fun j => sumR m' (fun i => f i j)) (fun j => f m' j)

theorem sumR_succ_shift (n : Nat) (f : Nat → R) :
    sumR (n + 1) f = f 0 + sumR n (fun i => f (i + 1)) := by
  induction n with
  | zero => simp [sumR, CRing.zero_add]
  | succ m ih =>
    rw [sumR_succ, ih, sumR_succ, CRing.add_assoc]

theorem sumR_extend {m n : Nat} (hmn : m ≤ n) {f : Nat → R}
    (hz : ∀ i, m ≤ i → i < n → f i = 0) :
    sumR m f = sumR n f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero => simp
  | succ k' ih =>
    have hprev : sumR m f = sumR (m + k') f :=
      ih (by omega) (fun i hi1 hi2 => hz i hi1 (by omega))
    have hlast : f (m + k') = 0 := hz (m + k') (by omega) (by omega)
    have hstep : m + (k' + 1) = (m + k') + 1 := by omega
    rw [hstep, sumR_succ, ← hprev, hlast, CRing.add_zero]

theorem sumR_single {n j : Nat} (hj : j < n) (v : R) :
    sumR n (fun i => if i = j then v else 0) = v := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [sumR_succ]
    by_cases hjm : j = m
    · subst hjm
      have hzero : sumR j (fun i => if i = j then v else 0) = 0 :=
        sumR_eq_zero (fun i hi => by
          have hne : i ≠ j := by omega
          simp only [hne, ↓reduceIte])
      rw [hzero, CRing.zero_add]
      simp only [↓reduceIte]
    · have hjlt : j < m := by omega
      have hne : m ≠ j := by omega
      rw [ih hjlt]
      simp only [hne, ↓reduceIte, CRing.add_zero]

theorem natCast_sumNat (n : Nat) (f : Nat → Nat) :
    (CRing.natCast (sumNat n f) : R) = sumR n (fun i => CRing.natCast (f i)) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumNat_succ, CRing.natCast_add, ih, sumR_succ]

theorem natCast_pow (a k : Nat) :
    (CRing.natCast (a ^ k) : R) = CRing.pow (CRing.natCast a) k := by
  induction k with
  | zero => simp [CRing.pow]
  | succ m ih =>
    rw [Nat.pow_succ, CRing.natCast_mul, ih, CRing.pow]

theorem natCast_mod_eq {p : Nat} (hchar : (CRing.natCast p : R) = 0) (n : Nat) :
    (CRing.natCast (n % p) : R) = CRing.natCast n := by
  have hdiv : n = p * (n / p) + n % p := (Nat.div_add_mod n p).symm
  conv => rhs; rw [hdiv]
  rw [CRing.natCast_add, CRing.natCast_mul, hchar, CRing.zero_mul, CRing.zero_add]

private theorem add_four_reassoc (A B C D : R) :
    (A + B) + (C + D) = (C + (A + D)) + B := by
  calc
    (A + B) + (C + D) = A + (B + (C + D)) := CRing.add_assoc _ _ _
    _ = A + ((C + D) + B) := by rw [CRing.add_comm B (C + D)]
    _ = (A + (C + D)) + B := (CRing.add_assoc _ _ _).symm
    _ = ((A + C) + D) + B := by rw [← CRing.add_assoc A C D]
    _ = ((C + A) + D) + B := by rw [CRing.add_comm A C]
    _ = (C + (A + D)) + B := by rw [CRing.add_assoc C A D]

private theorem mul_five_reassoc (S C A X U : R) :
    S * (C * ((A * X) * U)) = (S * (C * A)) * (U * X) := by
  calc
    S * (C * ((A * X) * U))
        = S * (C * (A * (X * U))) := by rw [CRing.mul_assoc A X U]
    _   = S * (C * (A * (U * X))) := by rw [CRing.mul_comm X U]
    _   = S * ((C * A) * (U * X)) := by rw [← CRing.mul_assoc C A (U * X)]
    _   = (S * (C * A)) * (U * X) := (CRing.mul_assoc S (C * A) (U * X)).symm

/-- Zero-Mathlib Binomial Theorem in an arbitrary commutative ring `R`. -/
theorem CRing.add_pow (y z : R) (k : Nat) :
    CRing.pow (y + z) k =
      sumR (k + 1) (fun d => CRing.natCast (choose k d) * (CRing.pow y d * CRing.pow z (k - d))) := by
  induction k with
  | zero =>
    simp [CRing.pow, sumR, choose, CRing.zero_add]
  | succ n ih =>
    rw [CRing.pow, ih, CRing.left_distrib]
    rw [← sumR_mul_right (n + 1) _ y, ← sumR_mul_right (n + 1) _ z]
    have hT1 :
        sumR (n + 1) (fun d =>
          CRing.natCast (choose n d) * (CRing.pow y d * CRing.pow z (n - d)) * y) =
        sumR (n + 1) (fun d =>
          CRing.natCast (choose n d) * (CRing.pow y (d + 1) * CRing.pow z (n - d))) := by
      refine sumR_congr (fun d _ => ?_)
      calc
        CRing.natCast (choose n d) * (CRing.pow y d * CRing.pow z (n - d)) * y
            = CRing.natCast (choose n d) * ((CRing.pow y d * CRing.pow z (n - d)) * y) :=
              CRing.mul_assoc _ _ _
        _   = CRing.natCast (choose n d) * (CRing.pow y d * (CRing.pow z (n - d) * y)) := by
              rw [CRing.mul_assoc (CRing.pow y d)]
        _   = CRing.natCast (choose n d) * (CRing.pow y d * (y * CRing.pow z (n - d))) := by
              rw [CRing.mul_comm (CRing.pow z (n - d)) y]
        _   = CRing.natCast (choose n d) * ((CRing.pow y d * y) * CRing.pow z (n - d)) := by
              rw [← CRing.mul_assoc (CRing.pow y d)]
        _   = CRing.natCast (choose n d) * (CRing.pow y (d + 1) * CRing.pow z (n - d)) := rfl
    have hT2 :
        sumR (n + 1) (fun d =>
          CRing.natCast (choose n d) * (CRing.pow y d * CRing.pow z (n - d)) * z) =
        CRing.natCast (choose n 0) * (CRing.pow y 0 * CRing.pow z (n + 1)) +
        sumR n (fun d =>
          CRing.natCast (choose n (d + 1)) * (CRing.pow y (d + 1) * CRing.pow z (n - d))) := by
      rw [sumR_succ_shift n]
      congr 1
      · simp only [Nat.sub_zero]
        rw [CRing.mul_assoc, CRing.mul_assoc]
        rfl
      · refine sumR_congr (fun d hd => ?_)
        have hsub : n - (d + 1) + 1 = n - d := by omega
        calc
          CRing.natCast (choose n (d + 1)) * (CRing.pow y (d + 1) * CRing.pow z (n - (d + 1))) * z
              = CRing.natCast (choose n (d + 1)) * (CRing.pow y (d + 1) * (CRing.pow z (n - (d + 1)) * z)) := by
                rw [CRing.mul_assoc, CRing.mul_assoc]
          _   = CRing.natCast (choose n (d + 1)) * (CRing.pow y (d + 1) * CRing.pow z (n - (d + 1) + 1)) := rfl
          _   = CRing.natCast (choose n (d + 1)) * (CRing.pow y (d + 1) * CRing.pow z (n - d)) := by
                rw [hsub]
    rw [hT1, hT2, sumR_succ n]
    have hRHS :
        sumR (n + 1 + 1) (fun d =>
          CRing.natCast (choose (n + 1) d) * (CRing.pow y d * CRing.pow z (n + 1 - d))) =
        CRing.natCast (choose n 0) * (CRing.pow y 0 * CRing.pow z (n + 1)) +
        sumR n (fun d =>
          (CRing.natCast (choose n d) + CRing.natCast (choose n (d + 1))) *
            (CRing.pow y (d + 1) * CRing.pow z (n - d))) +
        CRing.natCast (choose n n) * (CRing.pow y (n + 1) * CRing.pow z 0) := by
      rw [sumR_succ_shift (n + 1), sumR_succ n]
      have h0 : choose (n + 1) 0 = choose n 0 := by simp
      have hlast : choose (n + 1) (n + 1) = choose n n := by simp
      have hsubLast : n + 1 - (n + 1) = 0 := by omega
      rw [h0, hlast, hsubLast, ← CRing.add_assoc]
      congr 2
      refine sumR_congr (fun d _ => ?_)
      have hsub : n + 1 - (d + 1) = n - d := by omega
      rw [choose, CRing.natCast_add, hsub]
    rw [hRHS]
    have hMid :
        sumR n (fun d =>
          (CRing.natCast (choose n d) + CRing.natCast (choose n (d + 1))) *
            (CRing.pow y (d + 1) * CRing.pow z (n - d))) =
        sumR n (fun d => CRing.natCast (choose n d) * (CRing.pow y (d + 1) * CRing.pow z (n - d))) +
        sumR n (fun d => CRing.natCast (choose n (d + 1)) * (CRing.pow y (d + 1) * CRing.pow z (n - d))) := by
      rw [← sumR_add]
      refine sumR_congr (fun d _ => CRing.right_distrib _ _ _)
    rw [hMid]
    have hsubN : n - n = 0 := Nat.sub_self n
    rw [hsubN]
    exact add_four_reassoc _ _ _ _

end RingSums

/-! ## 2. Direct Literal `CRing` Execution and Soundness Bridge for `T1` -/

/-- Direct literal evaluation of univariate polynomial `poly` at `t` in any `CRing R`. -/
def evalPolyR {R : Type u} [CRing R] (poly : List Nat) (t : R) : R :=
  sumR poly.length (fun k => CRing.natCast (poly.getD k 0) * CRing.pow t k)

/-- Direct literal `CRing` execution of a single `Pass2Instr` (NO binomial formulas). -/
def Pass2Instr.execRing {R : Type u} [CRing R] (x : R) : R × R → Pass2Instr → R × R
  | (o, r), .addOut poly      => (o + evalPolyR poly r, r)
  | (o, r), .addWorkConst c   => (o, r + CRing.natCast c)
  | (o, r), .addInputOut lam  => (o + CRing.natCast lam * x, r)
  | (o, r), .addInputWork lam => (o, r + CRing.natCast lam * x)

/-- Direct literal `CRing` execution of a `Pass2Prog` over any `CRing R`. -/
def Pass2Prog.execRing {R : Type u} [CRing R] (x : R) : List Pass2Instr → R × R → R × R
  | [], st        => st
  | i :: rest, st => Pass2Prog.execRing x rest (i.execRing x st)

/-- Evaluate a formal bivariate coefficient table up to total degree `D` at `(u, x)`. -/
def evalState2Coeff {R : Type u} [CRing R] (D : Nat) (coeff : Nat → Nat → Nat) (u x : R) : R :=
  sumR (D + 1) (fun d =>
    sumR (d + 1) (fun dx =>
      CRing.natCast (coeff (d - dx) dx) * (CRing.pow u (d - dx) * CRing.pow x dx)))

/-- Maximum polynomial length occurring in any `addOut` instruction of `prog` (at least `1`). -/
def Pass2Prog.maxDeg : List Pass2Instr → Nat
  | [] => 1
  | .addOut poly :: rest => max poly.length (Pass2Prog.maxDeg rest)
  | _ :: rest => Pass2Prog.maxDeg rest

private theorem Pass2Prog.maxDeg_pos (prog : List Pass2Instr) : 1 ≤ Pass2Prog.maxDeg prog := by
  induction prog with
  | nil => exact Nat.le_refl 1
  | cons i rest ih =>
    cases i <;> simp only [Pass2Prog.maxDeg]
    · exact Nat.le_trans ih (Nat.le_max_right _ _)
    · exact ih
    · exact ih
    · exact ih

/-- Key trinomial identity: literal `evalPolyR poly (u + b + a*x)` matches `polyAtShiftCoeff`. -/
theorem evalPolyR_shift_eq_polyAtShiftCoeff {R : Type u} [CRing R]
    (poly : List Nat) (b a D : Nat) (hD : poly.length ≤ D + 1) (u x : R) :
    evalPolyR poly (u + CRing.natCast b + CRing.natCast a * x) =
      evalState2Coeff D (polyAtShiftCoeff poly b a) u x := by
  have hbase : u + CRing.natCast b + CRing.natCast a * x = (u + CRing.natCast a * x) + CRing.natCast b := by
    calc
      u + CRing.natCast b + CRing.natCast a * x
          = u + (CRing.natCast b + CRing.natCast a * x) := CRing.add_assoc _ _ _
      _   = u + (CRing.natCast a * x + CRing.natCast b) := by rw [CRing.add_comm (CRing.natCast b)]
      _   = (u + CRing.natCast a * x) + CRing.natCast b := (CRing.add_assoc _ _ _).symm
  unfold evalPolyR evalState2Coeff
  rw [hbase]
  have hterm : ∀ k < poly.length,
      CRing.natCast (poly.getD k 0) * CRing.pow ((u + CRing.natCast a * x) + CRing.natCast b) k =
      sumR (D + 1) (fun d =>
        CRing.natCast (poly.getD k 0 * choose k d * b ^ (k - d)) *
          CRing.pow (u + CRing.natCast a * x) d) := by
    intro k hk
    rw [CRing.add_pow (u + CRing.natCast a * x) (CRing.natCast b) k, ← sumR_mul_left]
    have hle : k + 1 ≤ D + 1 := by omega
    rw [sumR_extend hle (fun d hd1 _ => by
      have hcz : choose k d = 0 := choose_eq_zero_of_lt (by omega)
      simp [hcz])]
    refine sumR_congr (fun d _ => ?_)
    rw [CRing.natCast_mul, CRing.natCast_mul, natCast_pow]
    calc
      CRing.natCast (poly.getD k 0) *
          (CRing.natCast (choose k d) * (CRing.pow (u + CRing.natCast a * x) d * CRing.pow (CRing.natCast b) (k - d)))
          = (CRing.natCast (poly.getD k 0) * CRing.natCast (choose k d)) *
              (CRing.pow (CRing.natCast b) (k - d) * CRing.pow (u + CRing.natCast a * x) d) := by
            rw [← CRing.mul_assoc, CRing.mul_comm (CRing.pow (u + CRing.natCast a * x) d)]
      _   = (CRing.natCast (poly.getD k 0) * CRing.natCast (choose k d) * CRing.pow (CRing.natCast b) (k - d)) *
              CRing.pow (u + CRing.natCast a * x) d := (CRing.mul_assoc _ _ _).symm
  rw [sumR_congr hterm, sumR_swap]
  refine sumR_congr (fun d _ => ?_)
  rw [sumR_mul_right, ← natCast_sumNat]
  rw [CRing.add_comm u (CRing.natCast a * x), CRing.add_pow (CRing.natCast a * x) u d, ← sumR_mul_left]
  refine sumR_congr (fun dx hdx => ?_)
  have hdd : d - dx + dx = d := by omega
  simp only [polyAtShiftCoeff, hdd, CRing.natCast_mul, natCast_pow, CRing.mul_pow]
  exact mul_five_reassoc _ _ _ _ _

/-- Generalized per-program soundness invariant for `Pass2Prog.execFrom`. -/
theorem Pass2Prog.execRing_from_eq_evalState2 {R : Type u} [CRing R]
    {p : Nat} (hchar : (CRing.natCast p : R) = 0)
    (prog : List Pass2Instr) (D : Nat) (hD : Pass2Prog.maxDeg prog ≤ D)
    (st : State2) (o u x : R) :
    Pass2Prog.execRing x prog
        (o + evalState2Coeff D st.coeff u x, u + CRing.natCast st.b + CRing.natCast st.a * x) =
      let st' := Pass2Prog.execFrom p prog st
      (o + evalState2Coeff D st'.coeff u x, u + CRing.natCast st'.b + CRing.natCast st'.a * x) := by
  induction prog generalizing st with
  | nil => rfl
  | cons instr rest ih =>
    have hD_rest : Pass2Prog.maxDeg rest ≤ D := by
      cases instr <;> simp only [Pass2Prog.maxDeg] at hD
      · exact Nat.le_trans (Nat.le_max_right _ _) hD
      · exact hD
      · exact hD
      · exact hD
    cases instr with
    | addOut poly =>
      have hpoly : poly.length ≤ D + 1 := by
        simp only [Pass2Prog.maxDeg] at hD
        have := Nat.le_trans (Nat.le_max_left _ _) hD
        omega
      simp only [Pass2Prog.execRing, Pass2Instr.execRing, Pass2Prog.execFrom, Pass2Instr.exec]
      have hstep :
          (o + evalState2Coeff D st.coeff u x) + evalPolyR poly (u + CRing.natCast st.b + CRing.natCast st.a * x) =
          o + evalState2Coeff D (fun dR dx => (st.coeff dR dx + polyAtShiftCoeff poly st.b st.a dR dx) % p) u x := by
        rw [evalPolyR_shift_eq_polyAtShiftCoeff poly st.b st.a D hpoly u x, CRing.add_assoc]
        congr 1
        unfold evalState2Coeff
        rw [← sumR_add]
        refine sumR_congr (fun d _ => ?_)
        rw [← sumR_add]
        refine sumR_congr (fun dx _ => ?_)
        rw [natCast_mod_eq hchar, CRing.natCast_add, CRing.right_distrib]
      rw [hstep]
      exact ih hD_rest { st with coeff := fun dR dx => (st.coeff dR dx + polyAtShiftCoeff poly st.b st.a dR dx) % p }
    | addWorkConst c =>
      simp only [Pass2Prog.execRing, Pass2Instr.execRing, Pass2Prog.execFrom, Pass2Instr.exec]
      have hr :
          (u + CRing.natCast st.b + CRing.natCast st.a * x) + CRing.natCast c =
          u + CRing.natCast ((st.b + c) % p) + CRing.natCast st.a * x := by
        rw [natCast_mod_eq hchar, CRing.natCast_add]
        calc
          (u + CRing.natCast st.b + CRing.natCast st.a * x) + CRing.natCast c
              = (u + CRing.natCast st.b) + (CRing.natCast st.a * x + CRing.natCast c) := CRing.add_assoc _ _ _
          _   = (u + CRing.natCast st.b) + (CRing.natCast c + CRing.natCast st.a * x) := by
                rw [CRing.add_comm (CRing.natCast st.a * x)]
          _   = ((u + CRing.natCast st.b) + CRing.natCast c) + CRing.natCast st.a * x := (CRing.add_assoc _ _ _).symm
          _   = (u + (CRing.natCast st.b + CRing.natCast c)) + CRing.natCast st.a * x := by
                rw [CRing.add_assoc u]
      rw [hr]
      exact ih hD_rest { st with b := (st.b + c) % p }
    | addInputWork lam =>
      simp only [Pass2Prog.execRing, Pass2Instr.execRing, Pass2Prog.execFrom, Pass2Instr.exec]
      have hr :
          (u + CRing.natCast st.b + CRing.natCast st.a * x) + CRing.natCast lam * x =
          u + CRing.natCast st.b + CRing.natCast ((st.a + lam) % p) * x := by
        rw [natCast_mod_eq hchar, CRing.natCast_add, CRing.right_distrib, CRing.add_assoc]
      rw [hr]
      exact ih hD_rest { st with a := (st.a + lam) % p }
    | addInputOut lam =>
      have hD1 : 1 ≤ D := Nat.le_trans (Pass2Prog.maxDeg_pos rest) hD_rest
      simp only [Pass2Prog.execRing, Pass2Instr.execRing, Pass2Prog.execFrom, Pass2Instr.exec]
      have hlam :
          evalState2Coeff D (fun dR dx => if dR = 0 ∧ dx = 1 then lam else 0) u x =
          CRing.natCast lam * x := by
        unfold evalState2Coeff
        have hinner : ∀ d < D + 1,
            sumR (d + 1) (fun dx =>
              CRing.natCast (if d - dx = 0 ∧ dx = 1 then lam else 0) *
                (CRing.pow u (d - dx) * CRing.pow x dx)) =
            if d = 1 then CRing.natCast lam * x else 0 := by
          intro d _
          by_cases hd1 : d = 1
          · subst hd1
            simp [sumR, CRing.pow, CRing.zero_add, CRing.one_mul]
          · simp only [hd1, ↓reduceIte]
            refine sumR_eq_zero (fun dx hdx => ?_)
            have hcond : ¬ (d - dx = 0 ∧ dx = 1) := by omega
            simp [hcond]
        rw [sumR_congr hinner]
        exact sumR_single (by omega) (CRing.natCast lam * x)
      have hstep :
          (o + evalState2Coeff D st.coeff u x) + CRing.natCast lam * x =
          o + evalState2Coeff D (fun dR dx => (st.coeff dR dx + if dR = 0 ∧ dx = 1 then lam else 0) % p) u x := by
        rw [← hlam, CRing.add_assoc]
        congr 1
        unfold evalState2Coeff
        rw [← sumR_add]
        refine sumR_congr (fun d _ => ?_)
        rw [← sumR_add]
        refine sumR_congr (fun dx _ => ?_)
        rw [natCast_mod_eq hchar, CRing.natCast_add, CRing.right_distrib]
      rw [hstep]
      exact ih hD_rest { st with coeff := fun dR dx => (st.coeff dR dx + if dR = 0 ∧ dx = 1 then lam else 0) % p }

/--
**Exact Symbolic-to-Literal Ring Soundness for ALL `Pass2Prog`s:**
For EVERY `prog`, EVERY `p`, EVERY `CRing R` with `natCast p = 0`, and EVERY `o, u, x : R`,
literal ring execution agrees identically with symbolic `Pass2Prog.exec`.
-/
theorem Pass2Prog.execRing_eq_evalState2 {R : Type u} [CRing R]
    {p : Nat} (hchar : (CRing.natCast p : R) = 0)
    (prog : List Pass2Instr) (D : Nat) (hD : Pass2Prog.maxDeg prog ≤ D)
    (o u x : R) :
    Pass2Prog.execRing x prog (o, u) =
      let st := Pass2Prog.exec p prog
      (o + evalState2Coeff D st.coeff u x, u + CRing.natCast st.b + CRing.natCast st.a * x) := by
  have hinit :
      (o, u) =
      (o + evalState2Coeff D (fun _ _ => 0) u x,
       u + CRing.natCast 0 + CRing.natCast 0 * x) := by
    have hcz : evalState2Coeff D (fun _ _ => 0) u x = 0 := by
      unfold evalState2Coeff
      refine sumR_eq_zero (fun _ _ => sumR_eq_zero (fun _ _ => by simp))
    simp [hcz]
  conv => lhs; rw [hinit]
  exact Pass2Prog.execRing_from_eq_evalState2 hchar prog D hD ⟨0, 0, fun _ _ => 0⟩ o u x

/--
**Theorem `T1s` (Literal `CRing` Soundness of `CleanlyComputes2`):**
Whenever `CleanlyComputes2 p prog f` holds symbolically, literal ring execution of `prog` over
**every** characteristic-`p` commutative ring `R` cleanly maps `(o, u) ↦ (o + evalPolyR f x, u)`.
-/
theorem pass2_clean_implies_ring_exec {p : Nat} {prog : List Pass2Instr} {f : List Nat}
    (hclean : CleanlyComputes2 p prog f) :
    ∀ (R : Type) [CRing R], (CRing.natCast p : R) = 0 →
      ∀ o u x : R, Pass2Prog.execRing x prog (o, u) = (o + evalPolyR f x, u) := by
  intro R _ hchar o u x
  let D := max (Pass2Prog.maxDeg prog) f.length
  have hD : Pass2Prog.maxDeg prog ≤ D := Nat.le_max_left _ _
  have hfD : f.length ≤ D + 1 := by
    have := Nat.le_max_right (Pass2Prog.maxDeg prog) f.length
    omega
  rw [Pass2Prog.execRing_eq_evalState2 hchar prog D hD o u x]
  rcases hclean with ⟨hb, ha, hcoeff⟩
  have hbr : (CRing.natCast (Pass2Prog.exec p prog).b : R) = 0 := by
    rw [← natCast_mod_eq hchar, hb]; rfl
  have har : (CRing.natCast (Pass2Prog.exec p prog).a : R) = 0 := by
    rw [← natCast_mod_eq hchar, ha]; rfl
  have hO : evalState2Coeff D (Pass2Prog.exec p prog).coeff u x = evalPolyR f x := by
    unfold evalState2Coeff evalPolyR
    have hinner : ∀ d < D + 1,
        sumR (d + 1) (fun dx =>
          CRing.natCast ((Pass2Prog.exec p prog).coeff (d - dx) dx) *
            (CRing.pow u (d - dx) * CRing.pow x dx)) =
        CRing.natCast (f.getD d 0) * CRing.pow x d := by
      intro d _
      have hterm : ∀ dx < d + 1,
          CRing.natCast ((Pass2Prog.exec p prog).coeff (d - dx) dx) *
            (CRing.pow u (d - dx) * CRing.pow x dx) =
          if dx = d then CRing.natCast (f.getD d 0) * CRing.pow x d else 0 := by
        intro dx hdx
        rw [← natCast_mod_eq hchar, hcoeff (d - dx) dx, natCast_mod_eq hchar]
        by_cases hEq : dx = d
        · subst hEq
          simp [CRing.one_mul]
        · have hsub : d - dx ≠ 0 := by omega
          simp [hEq, hsub]
      rw [sumR_congr hterm]
      exact sumR_single (Nat.lt_succ_self d) _
    rw [sumR_congr hinner]
    symm
    exact sumR_extend hfD (fun d hd _ => by
      have hnone : f[d]? = none := List.getElem?_eq_none hd
      simp [List.getD, hnone])
  simp [hbr, har, hO]

/-! ## 3. Direct Literal `GF4`-Algebra Execution and Soundness Bridge for `T1e` -/

/-- Ring homomorphism `φ : GF4 → R` making an arbitrary `CRing R` a commutative `GF4`-algebra. -/
structure GF4Hom (R : Type u) [CRing R] where
  /-- The underlying map from the four-element field into the target ring. -/
  toFun : GF4 → R
  map_zero : toFun .z = 0
  map_one  : toFun .one = 1
  map_add  : ∀ a b : GF4, toFun (GF4.add a b) = toFun a + toFun b
  map_mul  : ∀ a b : GF4, toFun (GF4.mul a b) = toFun a * toFun b

/-- Identity homomorphism `GF4 → GF4` witnessing `GF4` as a `GF4`-algebra. -/
def GF4Hom.id : GF4Hom GF4 where
  toFun := fun a => a
  map_zero := rfl
  map_one  := rfl
  map_add  := fun _ _ => rfl
  map_mul  := fun _ _ => rfl

section GF4Alg

variable {R : Type u} [CRing R]

theorem GF4Hom.map_pow (φ : GF4Hom R) (a : GF4) (k : Nat) :
    φ.toFun (GF4.pow a k) = CRing.pow (φ.toFun a) k := by
  induction k with
  | zero => exact φ.map_one
  | succ m ih =>
    rw [GF4.pow, φ.map_mul, ih, CRing.pow, CRing.mul_comm]

theorem GF4Hom.char2 (φ : GF4Hom R) : (CRing.natCast 2 : R) = 0 := by
  have h1 : (CRing.natCast 2 : R) = 1 + 1 := by
    simp [CRing.natCast, CRing.zero_add]
  rw [h1, ← φ.map_one, ← φ.map_add]
  exact φ.map_zero

theorem GF4Hom.map_sumGF4 (φ : GF4Hom R) (n : Nat) (f : Nat → GF4) :
    φ.toFun (sumGF4 n f) = sumR n (fun i => φ.toFun (f i)) := by
  induction n with
  | zero => exact φ.map_zero
  | succ m ih =>
    rw [sumGF4, φ.map_add, ih, sumR_succ]

theorem GF4Hom.map_binomGF4 (φ : GF4Hom R) (n k : Nat) :
    φ.toFun (binomGF4 n k) = CRing.natCast (choose n k) := by
  rw [← natCast_mod_eq φ.char2 (choose n k)]
  unfold binomGF4
  have hlt : choose n k % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h1 : choose n k % 2 = 1
  · simp [h1, φ.map_one]
  · have h0 : choose n k % 2 = 0 := by omega
    simp [h0, φ.map_zero]

/-- Direct literal evaluation of a polynomial over `GF4` in any `GF4`-algebra `(R, φ)`. -/
def evalPolyGF4Alg (φ : GF4Hom R) (poly : List GF4) (t : R) : R :=
  sumR poly.length (fun k => φ.toFun (poly.getD k .z) * CRing.pow t k)

/-- Direct literal `GF4`-algebra execution of a single `Pass2GF4Instr` (NO binomial formulas). -/
def Pass2GF4Instr.execAlg (φ : GF4Hom R) (x : R) : R × R → Pass2GF4Instr → R × R
  | (o, r), .addOut poly      => (o + evalPolyGF4Alg φ poly r, r)
  | (o, r), .addWorkConst c   => (o, r + φ.toFun c)
  | (o, r), .addInputOut lam  => (o + φ.toFun lam * x, r)
  | (o, r), .addInputWork lam => (o, r + φ.toFun lam * x)

/-- Direct literal `GF4`-algebra execution of a `Pass2GF4Prog`. -/
def Pass2GF4Prog.execAlg (φ : GF4Hom R) (x : R) : List Pass2GF4Instr → R × R → R × R
  | [], st        => st
  | i :: rest, st => Pass2GF4Prog.execAlg φ x rest (i.execAlg φ x st)

/-- Evaluate a formal `GF4` bivariate coefficient table up to total degree `D` in `(R, φ)`. -/
def evalState2GF4Coeff (φ : GF4Hom R) (D : Nat) (coeff : Nat → Nat → GF4) (u x : R) : R :=
  sumR (D + 1) (fun d =>
    sumR (d + 1) (fun dx =>
      φ.toFun (coeff (d - dx) dx) * (CRing.pow u (d - dx) * CRing.pow x dx)))

/-- Maximum polynomial length occurring in any `addOut` instruction of a `Pass2GF4Prog`. -/
def Pass2GF4Prog.maxDeg : List Pass2GF4Instr → Nat
  | [] => 1
  | .addOut poly :: rest => max poly.length (Pass2GF4Prog.maxDeg rest)
  | _ :: rest => Pass2GF4Prog.maxDeg rest

private theorem Pass2GF4Prog.maxDeg_pos (prog : List Pass2GF4Instr) : 1 ≤ Pass2GF4Prog.maxDeg prog := by
  induction prog with
  | nil => exact Nat.le_refl 1
  | cons i rest ih =>
    cases i <;> simp only [Pass2GF4Prog.maxDeg]
    · exact Nat.le_trans ih (Nat.le_max_right _ _)
    · exact ih
    · exact ih
    · exact ih

theorem evalPolyGF4Alg_shift_eq_polyAtShiftCoeffGF4 (φ : GF4Hom R)
    (poly : List GF4) (b a : GF4) (D : Nat) (hD : poly.length ≤ D + 1) (u x : R) :
    evalPolyGF4Alg φ poly (u + φ.toFun b + φ.toFun a * x) =
      evalState2GF4Coeff φ D (polyAtShiftCoeffGF4 poly b a) u x := by
  have hbase : u + φ.toFun b + φ.toFun a * x = (u + φ.toFun a * x) + φ.toFun b := by
    calc
      u + φ.toFun b + φ.toFun a * x
          = u + (φ.toFun b + φ.toFun a * x) := CRing.add_assoc _ _ _
      _   = u + (φ.toFun a * x + φ.toFun b) := by rw [CRing.add_comm (φ.toFun b)]
      _   = (u + φ.toFun a * x) + φ.toFun b := (CRing.add_assoc _ _ _).symm
  unfold evalPolyGF4Alg evalState2GF4Coeff
  rw [hbase]
  have hterm : ∀ k < poly.length,
      φ.toFun (poly.getD k .z) * CRing.pow ((u + φ.toFun a * x) + φ.toFun b) k =
      sumR (D + 1) (fun d =>
        φ.toFun (GF4.mul (poly.getD k .z) (GF4.mul (binomGF4 k d) (GF4.pow b (k - d)))) *
          CRing.pow (u + φ.toFun a * x) d) := by
    intro k hk
    rw [CRing.add_pow (u + φ.toFun a * x) (φ.toFun b) k, ← sumR_mul_left]
    have hle : k + 1 ≤ D + 1 := by omega
    rw [sumR_extend hle (fun d hd1 _ => by
      have hcz : choose k d = 0 := choose_eq_zero_of_lt (by omega)
      simp [hcz])]
    refine sumR_congr (fun d _ => ?_)
    rw [φ.map_mul, φ.map_mul, φ.map_binomGF4, φ.map_pow]
    calc
      φ.toFun (poly.getD k .z) *
          (CRing.natCast (choose k d) * (CRing.pow (u + φ.toFun a * x) d * CRing.pow (φ.toFun b) (k - d)))
          = φ.toFun (poly.getD k .z) *
              (CRing.natCast (choose k d) * (CRing.pow (φ.toFun b) (k - d) * CRing.pow (u + φ.toFun a * x) d)) := by
            rw [CRing.mul_comm (CRing.pow (u + φ.toFun a * x) d)]
      _   = φ.toFun (poly.getD k .z) *
              ((CRing.natCast (choose k d) * CRing.pow (φ.toFun b) (k - d)) * CRing.pow (u + φ.toFun a * x) d) := by
            rw [← CRing.mul_assoc (CRing.natCast (choose k d))]
      _   = (φ.toFun (poly.getD k .z) * (CRing.natCast (choose k d) * CRing.pow (φ.toFun b) (k - d))) *
              CRing.pow (u + φ.toFun a * x) d := (CRing.mul_assoc _ _ _).symm
  rw [sumR_congr hterm, sumR_swap]
  refine sumR_congr (fun d _ => ?_)
  rw [sumR_mul_right, ← φ.map_sumGF4]
  rw [CRing.add_comm u (φ.toFun a * x), CRing.add_pow (φ.toFun a * x) u d, ← sumR_mul_left]
  refine sumR_congr (fun dx hdx => ?_)
  have hdd : d - dx + dx = d := by omega
  simp only [polyAtShiftCoeffGF4, hdd, φ.map_mul, φ.map_binomGF4, φ.map_pow, CRing.mul_pow]
  exact mul_five_reassoc _ _ _ _ _

theorem Pass2GF4Prog.execAlg_from_eq_evalState2GF4 (φ : GF4Hom R)
    (prog : List Pass2GF4Instr) (D : Nat) (hD : Pass2GF4Prog.maxDeg prog ≤ D)
    (st : State2GF4) (o u x : R) :
    Pass2GF4Prog.execAlg φ x prog
        (o + evalState2GF4Coeff φ D st.coeff u x, u + φ.toFun st.b + φ.toFun st.a * x) =
      let st' := Pass2GF4Prog.execFrom prog st
      (o + evalState2GF4Coeff φ D st'.coeff u x, u + φ.toFun st'.b + φ.toFun st'.a * x) := by
  induction prog generalizing st with
  | nil => rfl
  | cons instr rest ih =>
    have hD_rest : Pass2GF4Prog.maxDeg rest ≤ D := by
      cases instr <;> simp only [Pass2GF4Prog.maxDeg] at hD
      · exact Nat.le_trans (Nat.le_max_right _ _) hD
      · exact hD
      · exact hD
      · exact hD
    cases instr with
    | addOut poly =>
      have hpoly : poly.length ≤ D + 1 := by
        simp only [Pass2GF4Prog.maxDeg] at hD
        have := Nat.le_trans (Nat.le_max_left _ _) hD
        omega
      simp only [Pass2GF4Prog.execAlg, Pass2GF4Instr.execAlg, Pass2GF4Prog.execFrom, Pass2GF4Instr.exec]
      have hstep :
          (o + evalState2GF4Coeff φ D st.coeff u x) + evalPolyGF4Alg φ poly (u + φ.toFun st.b + φ.toFun st.a * x) =
          o + evalState2GF4Coeff φ D (fun dR dx => GF4.add (st.coeff dR dx) (polyAtShiftCoeffGF4 poly st.b st.a dR dx)) u x := by
        rw [evalPolyGF4Alg_shift_eq_polyAtShiftCoeffGF4 φ poly st.b st.a D hpoly u x, CRing.add_assoc]
        congr 1
        unfold evalState2GF4Coeff
        rw [← sumR_add]
        refine sumR_congr (fun d _ => ?_)
        rw [← sumR_add]
        refine sumR_congr (fun dx _ => ?_)
        rw [φ.map_add, CRing.right_distrib]
      rw [hstep]
      exact ih hD_rest { st with coeff := fun dR dx => GF4.add (st.coeff dR dx) (polyAtShiftCoeffGF4 poly st.b st.a dR dx) }
    | addWorkConst c =>
      simp only [Pass2GF4Prog.execAlg, Pass2GF4Instr.execAlg, Pass2GF4Prog.execFrom, Pass2GF4Instr.exec]
      have hr :
          (u + φ.toFun st.b + φ.toFun st.a * x) + φ.toFun c =
          u + φ.toFun (GF4.add st.b c) + φ.toFun st.a * x := by
        rw [φ.map_add]
        calc
          (u + φ.toFun st.b + φ.toFun st.a * x) + φ.toFun c
              = (u + φ.toFun st.b) + (φ.toFun st.a * x + φ.toFun c) := CRing.add_assoc _ _ _
          _   = (u + φ.toFun st.b) + (φ.toFun c + φ.toFun st.a * x) := by
                rw [CRing.add_comm (φ.toFun st.a * x)]
          _   = ((u + φ.toFun st.b) + φ.toFun c) + φ.toFun st.a * x := (CRing.add_assoc _ _ _).symm
          _   = (u + (φ.toFun st.b + φ.toFun c)) + φ.toFun st.a * x := by
                rw [CRing.add_assoc u]
      rw [hr]
      exact ih hD_rest { st with b := GF4.add st.b c }
    | addInputWork lam =>
      simp only [Pass2GF4Prog.execAlg, Pass2GF4Instr.execAlg, Pass2GF4Prog.execFrom, Pass2GF4Instr.exec]
      have hr :
          (u + φ.toFun st.b + φ.toFun st.a * x) + φ.toFun lam * x =
          u + φ.toFun st.b + φ.toFun (GF4.add st.a lam) * x := by
        rw [φ.map_add, CRing.right_distrib, CRing.add_assoc]
      rw [hr]
      exact ih hD_rest { st with a := GF4.add st.a lam }
    | addInputOut lam =>
      have hD1 : 1 ≤ D := Nat.le_trans (Pass2GF4Prog.maxDeg_pos rest) hD_rest
      simp only [Pass2GF4Prog.execAlg, Pass2GF4Instr.execAlg, Pass2GF4Prog.execFrom, Pass2GF4Instr.exec]
      have hlam :
          evalState2GF4Coeff φ D (fun dR dx => if dR = 0 ∧ dx = 1 then lam else .z) u x =
          φ.toFun lam * x := by
        unfold evalState2GF4Coeff
        have hinner : ∀ d < D + 1,
            sumR (d + 1) (fun dx =>
              φ.toFun (if d - dx = 0 ∧ dx = 1 then lam else .z) *
                (CRing.pow u (d - dx) * CRing.pow x dx)) =
            if d = 1 then φ.toFun lam * x else 0 := by
          intro d _
          by_cases hd1 : d = 1
          · subst hd1
            simp [sumR, CRing.pow, CRing.zero_add, CRing.one_mul, φ.map_zero]
          · simp only [hd1, ↓reduceIte]
            refine sumR_eq_zero (fun dx hdx => ?_)
            have hcond : ¬ (d - dx = 0 ∧ dx = 1) := by omega
            simp [hcond, φ.map_zero]
        rw [sumR_congr hinner]
        exact sumR_single (by omega) (φ.toFun lam * x)
      have hstep :
          (o + evalState2GF4Coeff φ D st.coeff u x) + φ.toFun lam * x =
          o + evalState2GF4Coeff φ D (fun dR dx => GF4.add (st.coeff dR dx) (if dR = 0 ∧ dx = 1 then lam else .z)) u x := by
        rw [← hlam, CRing.add_assoc]
        congr 1
        unfold evalState2GF4Coeff
        rw [← sumR_add]
        refine sumR_congr (fun d _ => ?_)
        rw [← sumR_add]
        refine sumR_congr (fun dx _ => ?_)
        rw [φ.map_add, CRing.right_distrib]
      rw [hstep]
      exact ih hD_rest { st with coeff := fun dR dx => GF4.add (st.coeff dR dx) (if dR = 0 ∧ dx = 1 then lam else .z) }

theorem Pass2GF4Prog.execAlg_eq_evalState2GF4 (φ : GF4Hom R)
    (prog : List Pass2GF4Instr) (D : Nat) (hD : Pass2GF4Prog.maxDeg prog ≤ D)
    (o u x : R) :
    Pass2GF4Prog.execAlg φ x prog (o, u) =
      let st := Pass2GF4Prog.exec prog
      (o + evalState2GF4Coeff φ D st.coeff u x, u + φ.toFun st.b + φ.toFun st.a * x) := by
  have hinit :
      (o, u) =
      (o + evalState2GF4Coeff φ D (fun _ _ => .z) u x,
       u + φ.toFun .z + φ.toFun .z * x) := by
    have hcz : evalState2GF4Coeff φ D (fun _ _ => .z) u x = 0 := by
      unfold evalState2GF4Coeff
      refine sumR_eq_zero (fun _ _ => sumR_eq_zero (fun _ _ => by simp [φ.map_zero]))
    simp [hcz, φ.map_zero]
  conv => lhs; rw [hinit]
  exact Pass2GF4Prog.execAlg_from_eq_evalState2GF4 φ prog D hD ⟨.z, .z, fun _ _ => .z⟩ o u x

end GF4Alg

/--
**Theorem `T1es` (Literal `GF4`-Algebra Soundness of `CleanlyComputes2GF4`):**
Whenever `CleanlyComputes2GF4 prog f` holds symbolically, literal execution of `prog` over
**every** commutative `GF4`-algebra `(R, φ)` (including `GF4` itself via `GF4Hom.id`)
cleanly maps `(o, u) ↦ (o + evalPolyGF4Alg φ f x, u)`.
-/
theorem pass2gf4_clean_implies_alg_exec {prog : List Pass2GF4Instr} {f : List GF4}
    (hclean : CleanlyComputes2GF4 prog f) :
    ∀ (R : Type) [CRing R] (φ : GF4Hom R) (o u x : R),
      Pass2GF4Prog.execAlg φ x prog (o, u) = (o + evalPolyGF4Alg φ f x, u) := by
  intro R _ φ o u x
  let D := max (Pass2GF4Prog.maxDeg prog) f.length
  have hD : Pass2GF4Prog.maxDeg prog ≤ D := Nat.le_max_left _ _
  have hfD : f.length ≤ D + 1 := by
    have := Nat.le_max_right (Pass2GF4Prog.maxDeg prog) f.length
    omega
  rw [Pass2GF4Prog.execAlg_eq_evalState2GF4 φ prog D hD o u x]
  rcases hclean with ⟨hb, ha, hcoeff⟩
  have hO : evalState2GF4Coeff φ D (Pass2GF4Prog.exec prog).coeff u x = evalPolyGF4Alg φ f x := by
    unfold evalState2GF4Coeff evalPolyGF4Alg
    have hinner : ∀ d < D + 1,
        sumR (d + 1) (fun dx =>
          φ.toFun ((Pass2GF4Prog.exec prog).coeff (d - dx) dx) *
            (CRing.pow u (d - dx) * CRing.pow x dx)) =
        φ.toFun (f.getD d .z) * CRing.pow x d := by
      intro d _
      have hterm : ∀ dx < d + 1,
          φ.toFun ((Pass2GF4Prog.exec prog).coeff (d - dx) dx) *
            (CRing.pow u (d - dx) * CRing.pow x dx) =
          if dx = d then φ.toFun (f.getD d .z) * CRing.pow x d else 0 := by
        intro dx hdx
        rw [hcoeff (d - dx) dx]
        by_cases hEq : dx = d
        · subst hEq
          simp [CRing.one_mul]
        · have hsub : d - dx ≠ 0 := by omega
          simp [hEq, hsub, φ.map_zero]
      rw [sumR_congr hterm]
      exact sumR_single (Nat.lt_succ_self d) _
    rw [sumR_congr hinner]
    symm
    exact sumR_extend hfD (fun d hd _ => by
      have hnone : f[d]? = none := List.getElem?_eq_none hd
      simp [List.getD, hnone, φ.map_zero])
  simp [hb, ha, φ.map_zero, hO]

end

end Catalytic
