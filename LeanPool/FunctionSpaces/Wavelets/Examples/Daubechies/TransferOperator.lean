/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.DaubechiesPolynomial
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The transfer operator

The **transfer operator** of order `N` acts on functions `g : ℝ → ℝ` by
`(T g)(ξ) = P(ξ/2) g(ξ/2) + P((ξ + 1)/2) g((ξ + 1)/2)` (`Daubechies.transfer`), where
`P(ξ) = P_N(sin²(πξ))` is the trigonometric Daubechies polynomial (`Daubechies.daubFun`). The
points `ξ/2` and `(ξ + 1)/2` are the two preimages of `ξ` under the doubling map `η ↦ 2η` modulo
`1`. The operator governs the decay of the symbol product `Φ(ξ) = ∏_{j ≥ 0} m_0(ξ/2^(j+1))` of a
Daubechies mask: `|Φ(ξ)|² = sinc(πξ)^(2N) ∏_{j ≥ 0} P(ξ/2^(j+1))`, and the finite products of
the factors `P(ξ/2^(j+1))` integrate to the integrals of the iterates `T^n 1`.

**Elementary properties.** `T` is linear and monotone, and it maps continuous functions to
continuous functions, `1`-periodic functions to `1`-periodic functions (from `ξ` to `ξ + 1` the
two points `ξ/2`, `(ξ + 1)/2` become `(ξ + 1)/2`, `ξ/2 + 1`, so the two summands swap) and
nonnegative functions to nonnegative ones. Since `0 ≤ P ≤ C(2N - 1, N)`,
`|T g| ≤ 2 C(2N - 1, N) sup |g|` (`Daubechies.abs_transfer_le`), and the same holds for the
iterates with the factor `(2 C(2N - 1, N))^n` (`Daubechies.abs_iterate_transfer_le`).

**The adjoint identity.** For continuous `1`-periodic `h` and `g`,
`∫_{-1/2}^{1/2} h(η) (T g)(η) dη = 2 ∫_{-1/2}^{1/2} h(2η) P(η) g(η) dη`
(`Daubechies.integral_transfer`). The substitutions `u = η/2` and `u = (η + 1)/2` turn the two
summands into integrals over `[-1/4, 1/4]` and `[1/4, 3/4]`, which together form one period of
the `1`-periodic function `u ↦ h(2u) P(u) g(u)`
(`Daubechies.integral_comp_div_two_add_comp_add_one_div_two`). By induction on `n`,
`∫_{-1/2}^{1/2} h(η) (T^n g)(η) dη = 2^n ∫_{-1/2}^{1/2} h(2^n η) ∏_{i<n} P(2^i η) g(η) dη`
(`Daubechies.integral_iterate_transfer`), and for `h = g = 1` the substitution `ξ = 2^n η` gives
`∫_{-2^n/2}^{2^n/2} ∏_{j<n} P(ξ/2^(j+1)) dξ = ∫_{-1/2}^{1/2} (T^n 1)(η) dη`
(`Daubechies.integral_prod_daubFun`).

**Growth bounds.** `Daubechies.TransferGrowth N λ C` says that `λ > 0` and `T^n 1 ≤ C λ^n`
everywhere, for every `n`; then the integrals above are at most `C λ^n`
(`Daubechies.TransferGrowth.integral_prod_daubFun_le`). The crude bound gives
`λ = 2 C(2N - 1, N)` and `C = 1` for every `N` (`Daubechies.transferGrowth_crude`).
-/

@[expose] public section

open Function

namespace Daubechies

/-! ### The operator and its elementary properties -/

/-- **The transfer operator** of order `N`: for `g : ℝ → ℝ` and `ξ ∈ ℝ`,
`(T g)(ξ) = P(ξ/2) g(ξ/2) + P((ξ + 1)/2) g((ξ + 1)/2)`, where `P = daubFun N` is the
trigonometric Daubechies polynomial `P(ξ) = P_N(sin²(πξ))`. The points `ξ/2` and `(ξ + 1)/2` are
the two preimages of `ξ` under the doubling map `η ↦ 2η` modulo `1`. -/
noncomputable def transfer (N : ℕ) (g : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  daubFun N (ξ / 2) * g (ξ / 2) + daubFun N ((ξ + 1) / 2) * g ((ξ + 1) / 2)

/-- `T` is additive: `T (g₁ + g₂) = T g₁ + T g₂`. -/
theorem transfer_add (N : ℕ) (g₁ g₂ : ℝ → ℝ) :
    transfer N (g₁ + g₂) = transfer N g₁ + transfer N g₂ := by
  ext ξ
  simp only [transfer, Pi.add_apply]
  ring

/-- `T` is homogeneous: `T (c g) = c T g` for every real `c`. -/
theorem transfer_smul (N : ℕ) (c : ℝ) (g : ℝ → ℝ) :
    transfer N (c • g) = c • transfer N g := by
  ext ξ
  simp only [transfer, Pi.smul_apply, smul_eq_mul]
  ring

/-- `T` maps `1`-periodic functions to `1`-periodic functions: from `ξ` to `ξ + 1` the points
`ξ/2` and `(ξ + 1)/2` become `(ξ + 1)/2` and `(ξ + 2)/2 = ξ/2 + 1`, so the two summands swap,
since `P` and `g` have period `1`. -/
theorem transfer_periodic (N : ℕ) {g : ℝ → ℝ} (hg : Periodic g 1) :
    Periodic (transfer N g) 1 := fun ξ => by
  have h : (ξ + 1 + 1) / 2 = ξ / 2 + 1 := by ring
  simp only [transfer, h, daubFun_periodic N (ξ / 2), hg (ξ / 2)]
  ring

/-- `T` maps continuous functions to continuous functions. -/
theorem continuous_transfer (N : ℕ) {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous (transfer N g) := by
  have hP := continuous_daubFun N
  unfold transfer
  fun_prop

/-- `T` is positive: `T g ≥ 0` for `g ≥ 0`, since `P ≥ 0`. -/
theorem transfer_nonneg (N : ℕ) {g : ℝ → ℝ} (hg : ∀ x, 0 ≤ g x) (ξ : ℝ) :
    0 ≤ transfer N g ξ :=
  add_nonneg (mul_nonneg (daubFun_nonneg N _) (hg _)) (mul_nonneg (daubFun_nonneg N _) (hg _))

/-- `T` is monotone: `g₁ ≤ g₂` everywhere implies `T g₁ ≤ T g₂` everywhere, since `P ≥ 0`. -/
theorem transfer_mono (N : ℕ) {g₁ g₂ : ℝ → ℝ} (h : ∀ x, g₁ x ≤ g₂ x) (ξ : ℝ) :
    transfer N g₁ ξ ≤ transfer N g₂ ξ :=
  add_le_add (mul_le_mul_of_nonneg_left (h _) (daubFun_nonneg N _))
    (mul_le_mul_of_nonneg_left (h _) (daubFun_nonneg N _))

/-- **The crude bound**: if `|g(x)| ≤ B` for every `x`, then `|(T g)(ξ)| ≤ 2 C(2N - 1, N) B` for
every `ξ`, since `0 ≤ P ≤ C(2N - 1, N)` (`Daubechies.daubFun_le_choose`). -/
theorem abs_transfer_le (N : ℕ) {g : ℝ → ℝ} {B : ℝ} (hg : ∀ x, |g x| ≤ B) (ξ : ℝ) :
    |transfer N g ξ| ≤ 2 * ((2 * N - 1).choose N : ℝ) * B := by
  have key : ∀ x, |daubFun N x * g x| ≤ ((2 * N - 1).choose N : ℝ) * B := fun x => by
    rw [abs_mul, abs_of_nonneg (daubFun_nonneg N x)]
    exact mul_le_mul (daubFun_le_choose N x) (hg x) (abs_nonneg _) (Nat.cast_nonneg _)
  calc |transfer N g ξ| ≤ |daubFun N (ξ / 2) * g (ξ / 2)| +
        |daubFun N ((ξ + 1) / 2) * g ((ξ + 1) / 2)| := abs_add_le _ _
    _ ≤ ((2 * N - 1).choose N : ℝ) * B + ((2 * N - 1).choose N : ℝ) * B :=
        add_le_add (key _) (key _)
    _ = 2 * ((2 * N - 1).choose N : ℝ) * B := by ring

/-! ### The iterates -/

/-- The iterates `T^n g` of a continuous `g` are continuous. -/
theorem continuous_iterate_transfer (N : ℕ) {g : ℝ → ℝ} (hg : Continuous g) (n : ℕ) :
    Continuous ((transfer N)^[n] g) := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    rw [iterate_succ_apply']
    exact continuous_transfer N ih

/-- The iterates `T^n g` of a `1`-periodic `g` are `1`-periodic. -/
theorem periodic_iterate_transfer (N : ℕ) {g : ℝ → ℝ} (hg : Periodic g 1) (n : ℕ) :
    Periodic ((transfer N)^[n] g) 1 := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    rw [iterate_succ_apply']
    exact transfer_periodic N ih

/-- The iterates `T^n g` of a nonnegative `g` are nonnegative. -/
theorem iterate_transfer_nonneg (N : ℕ) {g : ℝ → ℝ} (hg : ∀ x, 0 ≤ g x) (n : ℕ) (ξ : ℝ) :
    0 ≤ (transfer N)^[n] g ξ := by
  induction n generalizing ξ with
  | zero => exact hg ξ
  | succ n ih =>
    rw [iterate_succ_apply']
    exact transfer_nonneg N ih ξ

/-- If `|g(x)| ≤ B` for every `x`, then `|(T^n g)(ξ)| ≤ (2 C(2N - 1, N))^n B` for every `n` and
`ξ`, by induction from `Daubechies.abs_transfer_le`. -/
theorem abs_iterate_transfer_le (N : ℕ) {g : ℝ → ℝ} {B : ℝ} (hg : ∀ x, |g x| ≤ B) (n : ℕ)
    (ξ : ℝ) : |(transfer N)^[n] g ξ| ≤ (2 * ((2 * N - 1).choose N : ℝ)) ^ n * B := by
  induction n generalizing ξ with
  | zero => simpa using hg ξ
  | succ n ih =>
    rw [iterate_succ_apply', pow_succ', mul_assoc]
    exact abs_transfer_le N ih ξ

/-- The iterates `T^n 1` of the constant function `1` are continuous. -/
theorem continuous_iterate_transfer_one (N n : ℕ) :
    Continuous ((transfer N)^[n] (fun _ => 1)) :=
  continuous_iterate_transfer N continuous_const n

/-- The iterates `T^n 1` of the constant function `1` are `1`-periodic. -/
theorem periodic_iterate_transfer_one (N n : ℕ) :
    Periodic ((transfer N)^[n] (fun _ => 1)) 1 :=
  periodic_iterate_transfer N (fun _ => rfl) n

/-- The iterates `T^n 1` of the constant function `1` are nonnegative. -/
theorem iterate_transfer_one_nonneg (N n : ℕ) (ξ : ℝ) : 0 ≤ (transfer N)^[n] (fun _ => 1) ξ :=
  iterate_transfer_nonneg N (fun _ => zero_le_one) n ξ

/-! ### The adjoint identity -/

/-- If `h` has period `1`, then so has `η ↦ h(2η)`: `h` has period `2`, so `η ↦ h(2η)` has period
`2⁻¹ · 2 = 1` (Mathlib's `Function.Periodic.nat_mul` and `Function.Periodic.const_mul`). -/
theorem periodic_comp_two_mul {h : ℝ → ℝ} (hh : Periodic h 1) :
    Periodic (fun η => h (2 * η)) 1 := by
  simpa using (hh.nat_mul 2).const_mul (2 : ℝ)

/-- **The two branches of halving**: for a continuous `1`-periodic `f`,
`∫_{-1/2}^{1/2} (f(η/2) + f((η + 1)/2)) dη = 2 ∫_{-1/2}^{1/2} f(η) dη`. The substitutions
`u = η/2` and `u = (η + 1)/2` (Mathlib's `intervalIntegral.integral_comp_div` and
`intervalIntegral.integral_comp_div_add`) turn the two summands into `2 ∫_{-1/4}^{1/4} f` and
`2 ∫_{1/4}^{3/4} f`. Together they give `2 ∫_{-1/4}^{3/4} f`, and the integral of a `1`-periodic
function is the same over every interval of length `1`
(`Function.Periodic.intervalIntegral_add_eq`). -/
theorem integral_comp_div_two_add_comp_add_one_div_two {f : ℝ → ℝ} (hf : Continuous f)
    (hp : Periodic f 1) :
    ∫ η in (-1/2 : ℝ)..1/2, (f (η / 2) + f ((η + 1) / 2)) =
      2 * ∫ η in (-1/2 : ℝ)..1/2, f η := by
  have h1 : ∫ η in (-1/2 : ℝ)..1/2, f (η / 2) = 2 * ∫ η in (-1/4 : ℝ)..1/4, f η := by
    rw [intervalIntegral.integral_comp_div f two_ne_zero, smul_eq_mul]
    norm_num
  have h2 : ∫ η in (-1/2 : ℝ)..1/2, f ((η + 1) / 2) = 2 * ∫ η in (1/4 : ℝ)..3/4, f η := by
    simp only [add_div]
    rw [intervalIntegral.integral_comp_div_add f two_ne_zero, smul_eq_mul]
    norm_num
  have h3 : ∫ η in (-1/4 : ℝ)..3/4, f η = ∫ η in (-1/2 : ℝ)..1/2, f η := by
    have h := hp.intervalIntegral_add_eq (-1/4) (-1/2)
    rwa [show (-1/4 : ℝ) + 1 = 3/4 by norm_num, show (-1/2 : ℝ) + 1 = 1/2 by norm_num] at h
  rw [intervalIntegral.integral_add, h1, h2, ← mul_add,
    intervalIntegral.integral_add_adjacent_intervals, h3]
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- **The adjoint identity of the transfer operator**: for continuous `1`-periodic `h` and `g`,
`∫_{-1/2}^{1/2} h(η) (T g)(η) dη = 2 ∫_{-1/2}^{1/2} h(2η) P(η) g(η) dη`. With
`f(u) = h(2u) P(u) g(u)`, which is continuous and `1`-periodic, the integrand on the left is
`f(η/2) + f((η + 1)/2)`, because `h(η) = h(η + 1)`; then
`Daubechies.integral_comp_div_two_add_comp_add_one_div_two` applies. -/
theorem integral_transfer (N : ℕ) {h g : ℝ → ℝ} (hhc : Continuous h) (hhp : Periodic h 1)
    (hgc : Continuous g) (hgp : Periodic g 1) :
    ∫ η in (-1/2 : ℝ)..1/2, h η * transfer N g η =
      2 * ∫ η in (-1/2 : ℝ)..1/2, h (2 * η) * daubFun N η * g η := by
  have hP := continuous_daubFun N
  have hfc : Continuous fun u => h (2 * u) * daubFun N u * g u := by fun_prop
  have hfp : Periodic (fun u => h (2 * u) * daubFun N u * g u) 1 :=
    ((periodic_comp_two_mul hhp).mul (daubFun_periodic N)).mul hgp
  rw [← integral_comp_div_two_add_comp_add_one_div_two hfc hfp]
  refine intervalIntegral.integral_congr fun η _ => ?_
  simp only [transfer, show 2 * (η / 2) = η by ring, show 2 * ((η + 1) / 2) = η + 1 by ring,
    hhp η]
  ring

/-- **The adjoint identity for the iterates**: for continuous `1`-periodic `h` and `g` and every
`n`, `∫_{-1/2}^{1/2} h(η) (T^n g)(η) dη = 2^n ∫_{-1/2}^{1/2} h(2^n η) ∏_{i<n} P(2^i η) g(η) dη`.
Induction on `n`: `T^(n+1) g = T (T^n g)`, `Daubechies.integral_transfer` for `T^n g`, and the
induction hypothesis for the continuous `1`-periodic function `η ↦ h(2η) P(η)` in place of
`h`. -/
theorem integral_iterate_transfer (N n : ℕ) {h g : ℝ → ℝ} (hhc : Continuous h)
    (hhp : Periodic h 1) (hgc : Continuous g) (hgp : Periodic g 1) :
    ∫ η in (-1/2 : ℝ)..1/2, h η * (transfer N)^[n] g η =
      2 ^ n * ∫ η in (-1/2 : ℝ)..1/2,
        h (2 ^ n * η) * (∏ i ∈ Finset.range n, daubFun N (2 ^ i * η)) * g η := by
  induction n generalizing h with
  | zero => simp
  | succ n ih =>
    have hP := continuous_daubFun N
    have hc : Continuous fun η => h (2 * η) * daubFun N η := by fun_prop
    have hp : Periodic (fun η => h (2 * η) * daubFun N η) 1 :=
      (periodic_comp_two_mul hhp).mul (daubFun_periodic N)
    rw [iterate_succ_apply', integral_transfer N hhc hhp (continuous_iterate_transfer N hgc n)
      (periodic_iterate_transfer N hgp n), ih hc hp, ← mul_assoc, ← pow_succ']
    congr 1
    refine intervalIntegral.integral_congr fun η _ => ?_
    simp only [Finset.prod_range_succ, show (2 : ℝ) ^ (n + 1) * η = 2 * (2 ^ n * η) by ring]
    ring

/-- The adjoint identity for `h = g = 1`:
`∫_{-1/2}^{1/2} (T^n 1)(η) dη = 2^n ∫_{-1/2}^{1/2} ∏_{i<n} P(2^i η) dη`. -/
theorem integral_iterate_transfer_one (N n : ℕ) :
    ∫ η in (-1/2 : ℝ)..1/2, (transfer N)^[n] (fun _ => 1) η =
      2 ^ n * ∫ η in (-1/2 : ℝ)..1/2, ∏ i ∈ Finset.range n, daubFun N (2 ^ i * η) := by
  have h := integral_iterate_transfer N n (h := fun _ => 1) (g := fun _ => 1) continuous_const
    (fun _ => rfl) continuous_const (fun _ => rfl)
  simpa only [one_mul, mul_one] using h

/-- Reindexing a dyadic product by `j = n - 1 - i`:
`∏_{j<n} P(2^n η / 2^(j+1)) = ∏_{i<n} P(2^i η)`, since `2^n / 2^(j+1) = 2^(n-1-j)` for `j < n`
(Mathlib's `Finset.prod_range_reflect`). -/
theorem prod_daubFun_two_pow_mul_div (N n : ℕ) (η : ℝ) :
    ∏ j ∈ Finset.range n, daubFun N (2 ^ n * η / 2 ^ (j + 1)) =
      ∏ i ∈ Finset.range n, daubFun N (2 ^ i * η) := by
  rw [← Finset.prod_range_reflect (fun i => daubFun N (2 ^ i * η)) n]
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have h2 : (2 : ℝ) ^ n = 2 ^ (n - 1 - j) * 2 ^ (j + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h2, mul_right_comm, mul_div_cancel_right₀ _ (by positivity)]

/-- **The dyadic products integrate to the iterates of the transfer operator**: for every `n`,
`∫_{-2^n/2}^{2^n/2} ∏_{j<n} P(ξ/2^(j+1)) dξ = ∫_{-1/2}^{1/2} (T^n 1)(η) dη`. The substitution
`ξ = 2^n η` (Mathlib's `intervalIntegral.smul_integral_comp_mul_left`) turns the left side into
`2^n ∫_{-1/2}^{1/2} ∏_{j<n} P(2^n η/2^(j+1)) dη = 2^n ∫_{-1/2}^{1/2} ∏_{i<n} P(2^i η) dη`, which is
`Daubechies.integral_iterate_transfer_one`. -/
theorem integral_prod_daubFun (N n : ℕ) :
    ∫ ξ in -(2 ^ n / 2 : ℝ)..2 ^ n / 2, ∏ j ∈ Finset.range n, daubFun N (ξ / 2 ^ (j + 1)) =
      ∫ η in (-1/2 : ℝ)..1/2, (transfer N)^[n] (fun _ => 1) η := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (fun ξ => ∏ j ∈ Finset.range n, daubFun N (ξ / 2 ^ (j + 1))) ((2 : ℝ) ^ n)
    (a := -1/2) (b := 1/2)
  rw [show (2 : ℝ) ^ n * (-1/2) = -(2 ^ n / 2) by ring,
    show (2 : ℝ) ^ n * (1/2) = 2 ^ n / 2 by ring, smul_eq_mul] at h
  rw [← h, integral_iterate_transfer_one]
  congr 1
  exact intervalIntegral.integral_congr fun η _ => prod_daubFun_two_pow_mul_div N n η

/-! ### Growth bounds -/

/-- **A growth bound for the transfer operator** of order `N`, with rate `λ` (the argument `lam`)
and constant `C`: `λ > 0`, and `(T^n 1)(ξ) ≤ C λ^n` for every `n ∈ ℕ` and every `ξ ∈ ℝ`. Such a
bound controls the decay of the symbol product `Φ` of a Daubechies mask of order `N`:
`∫ (1 + |ξ|)^(2s) |Φ(ξ)|² dξ < ∞` for `s < N - log₄ λ`. It is a hypothesis; it is proved with
`λ = 4` for `N = 2`, `λ = 9` for `N = 3` (`Daubechies.transferGrowth_two`,
`Daubechies.transferGrowth_three`) and with a crude rate for every `N`
(`Daubechies.transferGrowth_crude`). -/
def TransferGrowth (N : ℕ) (lam C : ℝ) : Prop :=
  0 < lam ∧ ∀ (n : ℕ) (ξ : ℝ), (transfer N)^[n] (fun _ => 1) ξ ≤ C * lam ^ n

/-- A growth bound `T^n 1 ≤ C λ^n` forces `C ≥ 1`: for `n = 0` it says `1 ≤ C`. -/
theorem TransferGrowth.one_le {N : ℕ} {lam C : ℝ} (hg : TransferGrowth N lam C) : 1 ≤ C := by
  simpa using hg.2 0 0

/-- Under a growth bound `T^n 1 ≤ C λ^n`, the integral of `T^n 1` over one period is at most
`C λ^n`. -/
theorem TransferGrowth.integral_iterate_transfer_one_le {N : ℕ} {lam C : ℝ}
    (hg : TransferGrowth N lam C) (n : ℕ) :
    ∫ η in (-1/2 : ℝ)..1/2, (transfer N)^[n] (fun _ => 1) η ≤ C * lam ^ n := by
  have h := intervalIntegral.integral_mono (μ := MeasureTheory.volume) (a := -1/2) (b := 1/2)
    (by norm_num) ((continuous_iterate_transfer_one N n).intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _) (hg.2 n)
  rwa [intervalIntegral.integral_const, smul_eq_mul, show (1/2 : ℝ) - (-1/2) = 1 by norm_num,
    one_mul] at h

/-- Under a growth bound `T^n 1 ≤ C λ^n`, the dyadic products satisfy
`∫_{-2^n/2}^{2^n/2} ∏_{j<n} P(ξ/2^(j+1)) dξ ≤ C λ^n` (`Daubechies.integral_prod_daubFun`). -/
theorem TransferGrowth.integral_prod_daubFun_le {N : ℕ} {lam C : ℝ}
    (hg : TransferGrowth N lam C) (n : ℕ) :
    ∫ ξ in -(2 ^ n / 2 : ℝ)..2 ^ n / 2, ∏ j ∈ Finset.range n, daubFun N (ξ / 2 ^ (j + 1)) ≤
      C * lam ^ n := by
  rw [integral_prod_daubFun]
  exact hg.integral_iterate_transfer_one_le n

/-- **The crude growth bound**: `T^n 1 ≤ (2 C(2N - 1, N))^n` for every `N`, from
`|T g| ≤ 2 C(2N - 1, N) sup |g|` (`Daubechies.abs_iterate_transfer_le`). By
`Daubechies.choose_lt_four_pow`, `2 C(2N - 1, N) < 4^(N - 1/2)` for `N ≥ 2`. -/
theorem transferGrowth_crude (N : ℕ) : TransferGrowth N (2 * (2 * N - 1).choose N) 1 := by
  refine ⟨mul_pos two_pos (Nat.cast_pos.2 (Nat.choose_pos (by omega))), fun n ξ => ?_⟩
  have h := abs_iterate_transfer_le N (g := fun _ => 1) (B := 1) (fun _ => by simp) n ξ
  rw [mul_one] at h
  rw [one_mul]
  exact (le_abs_self _).trans h

end Daubechies
