/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Interpolation.Property
public import LeanPool.FunctionSpaces.ApproximationSpaces.Sequences.Hardy

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The reiteration theorem

For a couple `A = (N₀, N₁)` quasi-normed with constant `C`, the discrete K-norms
`‖u‖_{θ,q} = ‖(2^(-nθ) K(2^n, u))_{n ∈ ℤ}‖_{ℓ_q}` with `1 ≤ q ≤ ∞` are quasi-norms with the same
constant (`InterpCouple.discreteKMethodNorm_add_le` of `ApproximationSpaces.Interpolation.Couple`),
and they form the **couple of K-spaces**
`(‖·‖_{θ₀,q₀}, ‖·‖_{θ₁,q₁})` (`InterpCouple.kCouple`) and the endpoint couples
`(N₀, ‖·‖_{θ₁,q₁})` and `(‖·‖_{θ₀,q₀}, N₁)` (`InterpCouple.leftKCouple`,
`InterpCouple.rightKCouple`).  The classical reiteration results are in Bergh–Löfström,
Theorems 3.5.3 and 3.11.5, for complete intermediate spaces and an interior outer parameter.
Their quasi-normed result uses finite outer `q`. The membership comparison below uses the
stated quasi-norm laws and also permits infinite outer `q`. For `0 < θ₀ < θ₁ < 1`,
`0 < η < 1` and `θ = (1 - η) θ₀ + η θ₁`, it gives
`((X₀, X₁)_{θ₀,q₀}, (X₀, X₁)_{θ₁,q₁})_{η,q} = (X₀, X₁)_{θ,q}`
(`InterpCouple.memKMethod_kCouple_iff`), also for the continuous K-norms
(`InterpCouple.memKMethod_kMethodCouple_iff`), the endpoint couples
(`InterpCouple.memKMethod_leftKCouple_iff`, `InterpCouple.memKMethod_rightKCouple_iff`),
including `η = 0` on the left and `η = 1`
on the right, and the couples of bounded linear maps (`ApproximationScheme.memKMethod_reiteration`).

The inclusion `⊆` is the class `C_K` (Bergh–Löfström, Definition 3.5.1):
`K(2^n, a) ≤ 2^(nθ_i) ‖a‖_{θ_i,q_i}` gives `‖u‖_{θ,q} ≤ C ‖u‖_{η,q}` termwise
(`InterpCouple.discreteKMethodNorm_le_of_kFunctional_le`).  The inclusion `⊇` rests on
**Holmstedt's formula** (Holmstedt 1970; Bergh–Löfström, Theorem 3.6.1) in discrete form, with
`ℓ₁` sums in place of the `ℓ_{q_i}` norms of Theorem 3.6.1, which is enough for the reiteration
theorem: with `S₀(m) = ∑_{n < m} 2^(-nθ₀) K(2^n, u)` and `S₁(m) = ∑_{n ≥ m} 2^(-nθ₁) K(2^n, u)`
(`InterpCouple.kSumBelow`, `InterpCouple.kSumAbove`), the K-functional `KBar` of the couple of
K-spaces satisfies `KBar(2^(m(θ₁-θ₀)), u) ≤ c (S₀(m) + 2^(m(θ₁-θ₀)) S₁(m))`
(`InterpCouple.kFunctional_kCouple_le`; the endpoint versions are
`InterpCouple.kFunctional_leftKCouple_le` and `InterpCouple.kFunctional_rightKCouple_le`).  The
proof bounds the two discrete K-norms of `u - b` and `b` for every `b` by geometric sums and
takes the infimum over `b`.  Multiplied by
`2^(-mη(θ₁-θ₀))`, the two sums become the geometric convolutions of
`(2^(-nθ) K(2^n, u))_n` of `ApproximationSpaces.Sequences.Hardy`
(`InterpCouple.kCouple_discreteKMethodNorm_le`).  The constants are the named definitions
`InterpCouple.holmstedtConst`, `InterpCouple.reiterationConst` and their endpoint versions.
-/

@[expose] public section

open MeasureTheory Set Function
open scoped ENNReal
open ENNReal (lqNorm dyadicWeight)

namespace InterpCouple

open ENNReal (two_rpow_mul_two_rpow)

variable {U : Type*} [AddCommGroup U] {A : InterpCouple U} {C : ℝ≥0∞}
  {θ θ₀ θ₁ η ρ : ℝ} {q q₀ q₁ : ℝ≥0∞}

/-! ### Couples of K-spaces -/

/-- The **couple of two K-spaces** `((X₀, X₁)_{θ₀,q₀}, (X₀, X₁)_{θ₁,q₁})`, with the discrete
K-norms `‖u‖_{θ_i,q_i} = ‖(2^(-nθ_i) K(2^n, u))_{n ∈ ℤ}‖_{ℓ_{q_i}}` on the grid `t = 2^n`. -/
noncomputable def kCouple (A : InterpCouple U) (θ₀ : ℝ) (q₀ : ℝ≥0∞) (θ₁ : ℝ) (q₁ : ℝ≥0∞) :
    InterpCouple U :=
  ⟨A.discreteKMethodNorm θ₀ 1 q₀, A.discreteKMethodNorm θ₁ 1 q₁⟩

/-- The **left endpoint couple** `(X₀, (X₀, X₁)_{θ₁,q₁})`: the norm `N₀` and the discrete K-norm
`‖·‖_{θ₁,q₁}` on the grid `t = 2^n`. -/
noncomputable def leftKCouple (A : InterpCouple U) (θ₁ : ℝ) (q₁ : ℝ≥0∞) : InterpCouple U :=
  ⟨A.norm0, A.discreteKMethodNorm θ₁ 1 q₁⟩

/-- The **right endpoint couple** `((X₀, X₁)_{θ₀,q₀}, X₁)`: the discrete K-norm `‖·‖_{θ₀,q₀}` on
the grid `t = 2^n` and the norm `N₁`. -/
noncomputable def rightKCouple (A : InterpCouple U) (θ₀ : ℝ) (q₀ : ℝ≥0∞) : InterpCouple U :=
  ⟨A.discreteKMethodNorm θ₀ 1 q₀, A.norm1⟩

/-- The couple of two K-spaces with the **continuous K-norms** `‖·‖_{K,θ₀,q₀}` and
`‖·‖_{K,θ₁,q₁}`. -/
noncomputable def kMethodCouple (A : InterpCouple U) (θ₀ : ℝ) (q₀ : ℝ≥0∞) (θ₁ : ℝ)
    (q₁ : ℝ≥0∞) : InterpCouple U :=
  ⟨A.kMethodNorm θ₀ q₀, A.kMethodNorm θ₁ q₁⟩

/-- The couple of two K-spaces of a couple quasi-normed with constant `C` is quasi-normed with
constant `C`, for `q₀, q₁ ≥ 1`. -/
theorem isQuasiNormed_kCouple (hA : A.IsQuasiNormed C) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) :
    (A.kCouple θ₀ q₀ θ₁ q₁).IsQuasiNormed C where
  ne_top := hA.ne_top
  norm0_zero := discreteKMethodNorm_zero hA.norm0_zero hA.norm1_zero
  norm1_zero := discreteKMethodNorm_zero hA.norm0_zero hA.norm1_zero
  norm0_neg := discreteKMethodNorm_neg hA.norm0_neg hA.norm1_neg
  norm1_neg := discreteKMethodNorm_neg hA.norm0_neg hA.norm1_neg
  norm0_add_le := discreteKMethodNorm_add_le hA hq₀
  norm1_add_le := discreteKMethodNorm_add_le hA hq₁

/-- The left endpoint couple of a couple quasi-normed with constant `C` is quasi-normed with
constant `C`, for `q₁ ≥ 1`. -/
theorem isQuasiNormed_leftKCouple (hA : A.IsQuasiNormed C) (hq₁ : 1 ≤ q₁) :
    (A.leftKCouple θ₁ q₁).IsQuasiNormed C where
  ne_top := hA.ne_top
  norm0_zero := hA.norm0_zero
  norm1_zero := discreteKMethodNorm_zero hA.norm0_zero hA.norm1_zero
  norm0_neg := hA.norm0_neg
  norm1_neg := discreteKMethodNorm_neg hA.norm0_neg hA.norm1_neg
  norm0_add_le := hA.norm0_add_le
  norm1_add_le := discreteKMethodNorm_add_le hA hq₁

/-- The right endpoint couple of a couple quasi-normed with constant `C` is quasi-normed with
constant `C`, for `q₀ ≥ 1`. -/
theorem isQuasiNormed_rightKCouple (hA : A.IsQuasiNormed C) (hq₀ : 1 ≤ q₀) :
    (A.rightKCouple θ₀ q₀).IsQuasiNormed C where
  ne_top := hA.ne_top
  norm0_zero := discreteKMethodNorm_zero hA.norm0_zero hA.norm1_zero
  norm1_zero := hA.norm1_zero
  norm0_neg := discreteKMethodNorm_neg hA.norm0_neg hA.norm1_neg
  norm1_neg := hA.norm1_neg
  norm0_add_le := discreteKMethodNorm_add_le hA hq₀
  norm1_add_le := hA.norm1_add_le

/-- **The right endpoint couple is a swapped left endpoint couple**:
`((X₀, X₁)_{θ₀,q₀}, X₁)` is the swap of `(X₁, (X₁, X₀)_{1-θ₀,q₀})`, by
`discreteKMethodNorm_swap`. -/
theorem rightKCouple_eq_swap (A : InterpCouple U) (θ₀ : ℝ) (q₀ : ℝ≥0∞) :
    A.rightKCouple θ₀ q₀ = (A.swap.leftKCouple (1 - θ₀) q₀).swap := by
  have h : A.discreteKMethodNorm θ₀ 1 q₀ = A.swap.discreteKMethodNorm (1 - θ₀) 1 q₀ := by
    funext u
    rw [discreteKMethodNorm_swap, sub_sub_cancel]
  change (⟨A.discreteKMethodNorm θ₀ 1 q₀, A.norm1⟩ : InterpCouple U) =
    ⟨A.swap.discreteKMethodNorm (1 - θ₀) 1 q₀, A.norm1⟩
  rw [h]

/-! ### The easy inclusion: the class `C_K` -/

/-- The termwise bound behind `discreteKMethodNorm_le_of_kFunctional_le`: for a couple `A`
quasi-normed with constant `C` and a couple `B = (M₀, M₁)` with
`K_A(2^n, a) ≤ 2^(nθ_i) M_i(a)` for `i = 0, 1`, every `n ∈ ℤ` and every `a`, and for
`θ = (1 - η) θ₀ + η θ₁`, `2^(-nθ) K_A(2^n, u) ≤ C 2^(-n(θ₁-θ₀)η) K_B(2^(n(θ₁-θ₀)), u)`. -/
theorem discreteKSeq_le_of_kFunctional_le (hA : A.IsQuasiNormed C) {B : InterpCouple U}
    (h₀ : ∀ (n : ℤ) a, A.kFunctional (2 ^ (n : ℝ)) a ≤ 2 ^ ((n : ℝ) * θ₀) * B.norm0 a)
    (h₁ : ∀ (n : ℤ) a, A.kFunctional (2 ^ (n : ℝ)) a ≤ 2 ^ ((n : ℝ) * θ₁) * B.norm1 a)
    (η : ℝ) (u : U) (n : ℤ) :
    A.discreteKSeq ((1 - η) * θ₀ + η * θ₁) 1 u n ≤
      C * B.discreteKSeq η (θ₁ - θ₀) u n := by
  have hne : C * 2 ^ (-((n : ℝ) * (θ₁ - θ₀) * η)) ≠ ∞ :=
    ENNReal.mul_ne_top hA.ne_top (ENNReal.two_rpow_ne_top _)
  rw [discreteKSeq_one, discreteKSeq, ← mul_assoc]
  conv_rhs => rw [kFunctional, ENNReal.mul_iInf fun h => absurd h hne]
  refine le_iInf fun b => ?_
  have e₀ : (2 : ℝ≥0∞) ^ (-((n : ℝ) * ((1 - η) * θ₀ + η * θ₁))) * 2 ^ ((n : ℝ) * θ₀) =
      2 ^ (-((n : ℝ) * (θ₁ - θ₀) * η)) := by
    rw [two_rpow_mul_two_rpow]; congr 1; ring
  have e₁ : (2 : ℝ≥0∞) ^ (-((n : ℝ) * ((1 - η) * θ₀ + η * θ₁))) * 2 ^ ((n : ℝ) * θ₁) =
      2 ^ (-((n : ℝ) * (θ₁ - θ₀) * η)) * 2 ^ ((n : ℝ) * (θ₁ - θ₀)) := by
    rw [two_rpow_mul_two_rpow, two_rpow_mul_two_rpow]; congr 1; ring
  calc 2 ^ (-((n : ℝ) * ((1 - η) * θ₀ + η * θ₁))) * A.kFunctional (2 ^ (n : ℝ)) u
      = 2 ^ (-((n : ℝ) * ((1 - η) * θ₀ + η * θ₁))) *
          A.kFunctional (2 ^ (n : ℝ)) ((u - b) + b) := by rw [sub_add_cancel]
    _ ≤ 2 ^ (-((n : ℝ) * ((1 - η) * θ₀ + η * θ₁))) * (C * (2 ^ ((n : ℝ) * θ₀) * B.norm0 (u - b) +
          2 ^ ((n : ℝ) * θ₁) * B.norm1 b)) := by
        gcongr
        exact (kFunctional_add_le hA _ _).trans (by gcongr <;> simp only [h₀, h₁])
    _ = C * ((2 ^ (-((n : ℝ) * ((1 - η) * θ₀ + η * θ₁))) * 2 ^ ((n : ℝ) * θ₀)) * B.norm0 (u - b) +
          (2 ^ (-((n : ℝ) * ((1 - η) * θ₀ + η * θ₁))) * 2 ^ ((n : ℝ) * θ₁)) * B.norm1 b) := by
        ring
    _ = C * 2 ^ (-((n : ℝ) * (θ₁ - θ₀) * η)) *
          (B.norm0 (u - b) + 2 ^ ((n : ℝ) * (θ₁ - θ₀)) * B.norm1 b) := by
        rw [e₀, e₁]; ring

/-- **The easy inclusion of the reiteration theorem** (the class `C_K` of Bergh–Löfström,
Definition 3.5.1, and the first half of the proof of Theorem 3.5.3): let `A` be quasi-normed
with constant `C` and let `B = (M₀, M₁)` be a couple with `K_A(2^n, a) ≤ 2^(nθ_i) M_i(a)` for
`i = 0, 1`, every `n ∈ ℤ` and every `a`.  Then for `θ = (1 - η) θ₀ + η θ₁`, the discrete
K-norms of `A` on the grid `2^n` and of `B` on the grid `2^(n(θ₁-θ₀))` satisfy
`‖u‖_{θ,q} ≤ C ‖u‖^B_{η,q}`. -/
theorem discreteKMethodNorm_le_of_kFunctional_le (hA : A.IsQuasiNormed C) {B : InterpCouple U}
    (h₀ : ∀ (n : ℤ) a, A.kFunctional (2 ^ (n : ℝ)) a ≤ 2 ^ ((n : ℝ) * θ₀) * B.norm0 a)
    (h₁ : ∀ (n : ℤ) a, A.kFunctional (2 ^ (n : ℝ)) a ≤ 2 ^ ((n : ℝ) * θ₁) * B.norm1 a)
    (η : ℝ) (q : ℝ≥0∞) (u : U) :
    A.discreteKMethodNorm ((1 - η) * θ₀ + η * θ₁) 1 q u ≤
      C * B.discreteKMethodNorm η (θ₁ - θ₀) q u := by
  rw [discreteKMethodNorm, discreteKMethodNorm, ← ENNReal.lqNorm_const_mul]
  exact ENNReal.lqNorm_mono (discreteKSeq_le_of_kFunctional_le hA h₀ h₁ η u)

/-- **The easy inclusion for the couple of K-spaces**: for a couple quasi-normed with constant
`C`, `q₀, q₁ ≠ 0` and `θ = (1 - η) θ₀ + η θ₁`, `‖u‖_{θ,q} ≤ C ‖u‖_{η,q}`, where the right side is
the discrete K-norm of `kCouple` on the grid `t = 2^(n(θ₁-θ₀))`. -/
theorem discreteKMethodNorm_le_kCouple (hA : A.IsQuasiNormed C) (hq₀ : q₀ ≠ 0) (hq₁ : q₁ ≠ 0)
    (η : ℝ) (q : ℝ≥0∞) (u : U) :
    A.discreteKMethodNorm ((1 - η) * θ₀ + η * θ₁) 1 q u ≤
      C * (A.kCouple θ₀ q₀ θ₁ q₁).discreteKMethodNorm η (θ₁ - θ₀) q u :=
  discreteKMethodNorm_le_of_kFunctional_le hA
    (fun n a => kFunctional_two_rpow_le_discreteKMethodNorm hq₀ n a)
    (fun n a => kFunctional_two_rpow_le_discreteKMethodNorm hq₁ n a) η q u

/-- **The easy inclusion for the left endpoint couple**: for a couple quasi-normed with
constant `C` and `q₁ ≠ 0`, `‖u‖_{ηθ₁,q} ≤ C ‖u‖_{η,q}`, where the right side is the discrete
K-norm of `leftKCouple` on the grid `t = 2^(nθ₁)`. -/
theorem discreteKMethodNorm_le_leftKCouple (hA : A.IsQuasiNormed C) (hq₁ : q₁ ≠ 0) (η : ℝ)
    (q : ℝ≥0∞) (u : U) :
    A.discreteKMethodNorm (η * θ₁) 1 q u ≤
      C * (A.leftKCouple θ₁ q₁).discreteKMethodNorm η θ₁ q u := by
  have h := discreteKMethodNorm_le_of_kFunctional_le (θ₀ := 0) (B := A.leftKCouple θ₁ q₁) hA
    (fun n a => by
      rw [mul_zero, ENNReal.rpow_zero, one_mul]
      exact kFunctional_le_norm0 hA.norm1_zero a)
    (fun n a => kFunctional_two_rpow_le_discreteKMethodNorm hq₁ n a) η q u
  simpa only [mul_zero, zero_add, sub_zero] using h

/-- **The easy inclusion for the right endpoint couple**: for a couple quasi-normed with
constant `C` and `q₀ ≠ 0`, `‖u‖_{(1-η)θ₀+η,q} ≤ C ‖u‖_{η,q}`, where the right side is the
discrete K-norm of `rightKCouple` on the grid `t = 2^(n(1-θ₀))`. -/
theorem discreteKMethodNorm_le_rightKCouple (hA : A.IsQuasiNormed C) (hq₀ : q₀ ≠ 0) (η : ℝ)
    (q : ℝ≥0∞) (u : U) :
    A.discreteKMethodNorm ((1 - η) * θ₀ + η) 1 q u ≤
      C * (A.rightKCouple θ₀ q₀).discreteKMethodNorm η (1 - θ₀) q u := by
  have h := discreteKMethodNorm_le_of_kFunctional_le (θ₁ := 1) (B := A.rightKCouple θ₀ q₀) hA
    (fun n a => kFunctional_two_rpow_le_discreteKMethodNorm hq₀ n a)
    (fun n a => by
      rw [mul_one]
      exact kFunctional_le_mul_norm1 hA.norm0_zero a) η q u
  simpa only [mul_one] using h

/-! ### Holmstedt's formula -/

/-- The sum `S₀(m) = ∑_{n < m} 2^(-nθ) K(2^n, u)` of the terms below `m` of the discrete
K-method on the grid `t = 2^n`, indexed by `n = m - (j + 1)`, `j ∈ ℕ`. -/
noncomputable def kSumBelow (A : InterpCouple U) (θ : ℝ) (u : U) (m : ℤ) : ℝ≥0∞ :=
  ∑' j : ℕ, A.discreteKSeq θ 1 u (m - (j + 1))

/-- The sum `S₁(m) = ∑_{n ≥ m} 2^(-nθ) K(2^n, u)` of the terms from `m` on of the discrete
K-method on the grid `t = 2^n`, indexed by `n = m + j`, `j ∈ ℕ`. -/
noncomputable def kSumAbove (A : InterpCouple U) (θ : ℝ) (u : U) (m : ℤ) : ℝ≥0∞ :=
  ∑' j : ℕ, A.discreteKSeq θ 1 u (m + j)

/-- The discrete K-norm on the grid `2^n` is at most the sum of all its terms, split at `m`:
`‖v‖_{θ,q} ≤ S₁(m) + S₀(m)` for `q ≥ 1`. -/
theorem discreteKMethodNorm_le_kSumAbove_add_kSumBelow (hq : 1 ≤ q) (m : ℤ) (v : U) :
    A.discreteKMethodNorm θ 1 q v ≤ A.kSumAbove θ v m + A.kSumBelow θ v m :=
  (ENNReal.lqNorm_le_lqNorm_one hq _).trans_eq (ENNReal.tsum_int_eq_tsum_add_tsum_sub m _)

/-- **The sum from `m` on under a pointwise bound**: if `K(2^n, v) ≤ a K(2^n, u) + X` for every
`n ≥ m`, then `S₁(m; v) ≤ a S₁(m; u) + 2^(-mθ) (1 - 2^(-θ))⁻¹ X`. -/
theorem kSumAbove_le {u v : U} {a X : ℝ≥0∞} {m : ℤ}
    (h : ∀ n : ℤ, m ≤ n → A.kFunctional (2 ^ (n : ℝ)) v ≤
      a * A.kFunctional (2 ^ (n : ℝ)) u + X) :
    A.kSumAbove θ v m ≤
      a * A.kSumAbove θ u m + 2 ^ (-((m : ℝ) * θ)) * (1 - (2 : ℝ≥0∞) ^ (-θ))⁻¹ * X := by
  have hterm : ∀ j : ℕ, A.discreteKSeq θ 1 v (m + j) ≤
      a * A.discreteKSeq θ 1 u (m + j) + 2 ^ (-((m : ℝ) * θ)) * dyadicWeight (-θ) j * X := by
    intro j
    have e : (2 : ℝ≥0∞) ^ (-(((m + j : ℤ) : ℝ) * θ)) =
        2 ^ (-((m : ℝ) * θ)) * dyadicWeight (-θ) j := by
      rw [dyadicWeight, two_rpow_mul_two_rpow]
      congr 1
      push_cast
      ring
    rw [discreteKSeq_one, discreteKSeq_one]
    calc 2 ^ (-(((m + j : ℤ) : ℝ) * θ)) * A.kFunctional (2 ^ ((m + j : ℤ) : ℝ)) v
        ≤ 2 ^ (-(((m + j : ℤ) : ℝ) * θ)) * (a * A.kFunctional (2 ^ ((m + j : ℤ) : ℝ)) u + X) := by
          gcongr
          exact h _ (by omega)
      _ = _ := by rw [e]; ring
  calc A.kSumAbove θ v m ≤ ∑' j : ℕ, (a * A.discreteKSeq θ 1 u (m + j) +
        2 ^ (-((m : ℝ) * θ)) * dyadicWeight (-θ) j * X) := tsum_le_tsum hterm
    _ = _ := by
        rw [tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right,
          ENNReal.tsum_mul_left, ENNReal.tsum_dyadicWeight_neg]
        rfl

/-- **The sum below `m` under a pointwise bound**: if `K(2^n, v) ≤ a K(2^n, u) + 2^(n-m) X` for
every `n < m`, then `S₀(m; v) ≤ a S₀(m; u) + 2^(-mθ) (1 - 2^(-(1-θ)))⁻¹ X`. -/
theorem kSumBelow_le {u v : U} {a X : ℝ≥0∞} {m : ℤ}
    (h : ∀ n : ℤ, n < m → A.kFunctional (2 ^ (n : ℝ)) v ≤
      a * A.kFunctional (2 ^ (n : ℝ)) u + 2 ^ ((n : ℝ) - m) * X) :
    A.kSumBelow θ v m ≤
      a * A.kSumBelow θ u m + 2 ^ (-((m : ℝ) * θ)) * (1 - (2 : ℝ≥0∞) ^ (-(1 - θ)))⁻¹ * X := by
  have hterm : ∀ j : ℕ, A.discreteKSeq θ 1 v (m - (j + 1)) ≤ a * A.discreteKSeq θ 1 u (m - (j + 1))
      + 2 ^ (-((m : ℝ) * θ)) * dyadicWeight (-(1 - θ)) (j + 1) * X := by
    intro j
    have e : (2 : ℝ≥0∞) ^ (-(((m - (j + 1) : ℤ) : ℝ) * θ)) * 2 ^ (((m - (j + 1) : ℤ) : ℝ) - m) =
        2 ^ (-((m : ℝ) * θ)) * dyadicWeight (-(1 - θ)) (j + 1) := by
      rw [dyadicWeight, two_rpow_mul_two_rpow, two_rpow_mul_two_rpow]
      congr 1
      push_cast
      ring
    rw [discreteKSeq_one, discreteKSeq_one]
    calc 2 ^ (-(((m - (j + 1) : ℤ) : ℝ) * θ)) * A.kFunctional (2 ^ ((m - (j + 1) : ℤ) : ℝ)) v
        ≤ 2 ^ (-(((m - (j + 1) : ℤ) : ℝ) * θ)) * (a * A.kFunctional (2 ^ ((m - (j + 1) : ℤ) : ℝ)) u
          + 2 ^ (((m - (j + 1) : ℤ) : ℝ) - m) * X) := by
          gcongr
          exact h _ (by omega)
      _ = _ := by rw [← e]; ring
  calc A.kSumBelow θ v m ≤ ∑' j : ℕ, (a * A.discreteKSeq θ 1 u (m - (j + 1)) +
        2 ^ (-((m : ℝ) * θ)) * dyadicWeight (-(1 - θ)) (j + 1) * X) := tsum_le_tsum hterm
    _ = a * A.kSumBelow θ u m +
          2 ^ (-((m : ℝ) * θ)) * (∑' j : ℕ, dyadicWeight (-(1 - θ)) (j + 1)) * X := by
        rw [tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right,
          ENNReal.tsum_mul_left]
        rfl
    _ ≤ _ := by
        gcongr
        exact ENNReal.tsum_dyadicWeight_neg_succ_le _

/-- `K(2^n, b) ≤ 2^(n-m) (N₀(u - b) + 2^m N₁(b))` if `N₀(0) = 0`, since `K(2^n, b) ≤ 2^n N₁(b)`. -/
theorem kFunctional_le_two_rpow_sub_mul (h0 : A.norm0 0 = 0) (n m : ℤ) (u b : U) :
    A.kFunctional (2 ^ (n : ℝ)) b ≤
      2 ^ ((n : ℝ) - m) * (A.norm0 (u - b) + 2 ^ (m : ℝ) * A.norm1 b) :=
  calc A.kFunctional (2 ^ (n : ℝ)) b ≤ 2 ^ (n : ℝ) * A.norm1 b := kFunctional_le_mul_norm1 h0 b
    _ = 2 ^ ((n : ℝ) - m) * (2 ^ (m : ℝ) * A.norm1 b) := by
        rw [← mul_assoc, two_rpow_mul_two_rpow, sub_add_cancel]
    _ ≤ _ := by gcongr; exact le_add_self

/-- The constant `(1 - 2^(-α))⁻¹ + C (1 - 2^(-(1-α)))⁻¹` of one half of Holmstedt's formula. -/
noncomputable def holmstedtSideConst (C : ℝ≥0∞) (α : ℝ) : ℝ≥0∞ :=
  (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ + C * (1 - (2 : ℝ≥0∞) ^ (-(1 - α)))⁻¹

/-- The constant `holmstedtSideConst C α` is finite for `C < ∞` and `0 < α < 1`. -/
theorem holmstedtSideConst_ne_top {α : ℝ} (hC : C ≠ ∞) (hα : 0 < α) (hα' : α < 1) :
    holmstedtSideConst C α ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨ENNReal.one_sub_two_rpow_neg_inv_ne_top hα,
    ENNReal.mul_ne_top hC (ENNReal.one_sub_two_rpow_neg_inv_ne_top (sub_pos.2 hα'))⟩

/-- **The first half of Holmstedt's bound**: for a couple quasi-normed with constant `C`,
`q ≥ 1`, `m ∈ ℤ` and `u, b ∈ U`, with `J = N₀(u - b) + 2^m N₁(b)`,
`‖u - b‖_{θ,q} ≤ C S₀(m; u) + 2^(-mθ) holmstedtSideConst C θ · J`. -/
theorem discreteKMethodNorm_sub_le_kSumBelow (hA : A.IsQuasiNormed C) (hq : 1 ≤ q) (m : ℤ)
    (u b : U) :
    A.discreteKMethodNorm θ 1 q (u - b) ≤ C * A.kSumBelow θ u m + 2 ^ (-((m : ℝ) * θ)) *
      holmstedtSideConst C θ * (A.norm0 (u - b) + 2 ^ (m : ℝ) * A.norm1 b) := by
  have h₁ := kSumAbove_le (A := A) (θ := θ) (u := u) (v := u - b) (a := 0) (m := m)
    (X := A.norm0 (u - b) + 2 ^ (m : ℝ) * A.norm1 b) fun n _ => by
      rw [zero_mul, zero_add]
      exact (kFunctional_le_norm0 hA.norm1_zero _).trans le_self_add
  have h₂ := kSumBelow_le (A := A) (θ := θ) (u := u) (v := u - b) (a := C) (m := m)
    (X := C * (A.norm0 (u - b) + 2 ^ (m : ℝ) * A.norm1 b)) fun n _ => by
      calc A.kFunctional (2 ^ (n : ℝ)) (u - b)
          ≤ C * (A.kFunctional (2 ^ (n : ℝ)) u + A.kFunctional (2 ^ (n : ℝ)) (-b)) := by
            rw [sub_eq_add_neg]; exact kFunctional_add_le hA _ _
        _ ≤ C * (A.kFunctional (2 ^ (n : ℝ)) u + 2 ^ ((n : ℝ) - m) *
              (A.norm0 (u - b) + 2 ^ (m : ℝ) * A.norm1 b)) := by
            rw [kFunctional_neg hA.norm0_neg hA.norm1_neg]
            gcongr
            exact kFunctional_le_two_rpow_sub_mul hA.norm0_zero n m u b
        _ = _ := by ring
  calc A.discreteKMethodNorm θ 1 q (u - b) ≤ A.kSumAbove θ (u - b) m + A.kSumBelow θ (u - b) m :=
        discreteKMethodNorm_le_kSumAbove_add_kSumBelow hq m _
    _ ≤ _ := add_le_add h₁ h₂
    _ = _ := by rw [holmstedtSideConst]; ring

/-- **The second half of Holmstedt's bound**: for a couple quasi-normed with constant `C`,
`q ≥ 1`, `m ∈ ℤ` and `u, b ∈ U`, with `J = N₀(u - b) + 2^m N₁(b)`,
`‖b‖_{θ,q} ≤ C S₁(m; u) + 2^(-mθ) holmstedtSideConst C (1 - θ) · J`. -/
theorem discreteKMethodNorm_le_kSumAbove (hA : A.IsQuasiNormed C) (hq : 1 ≤ q) (m : ℤ)
    (u b : U) :
    A.discreteKMethodNorm θ 1 q b ≤ C * A.kSumAbove θ u m + 2 ^ (-((m : ℝ) * θ)) *
      holmstedtSideConst C (1 - θ) * (A.norm0 (u - b) + 2 ^ (m : ℝ) * A.norm1 b) := by
  have h₁ := kSumAbove_le (A := A) (θ := θ) (u := u) (v := b) (a := C) (m := m)
    (X := C * (A.norm0 (u - b) + 2 ^ (m : ℝ) * A.norm1 b)) fun n _ => by
      calc A.kFunctional (2 ^ (n : ℝ)) b
          ≤ C * (A.kFunctional (2 ^ (n : ℝ)) u + A.kFunctional (2 ^ (n : ℝ)) (-(u - b))) := by
            rw [show b = u + -(u - b) by abel]
            exact (kFunctional_add_le hA _ _).trans_eq (by rw [show u + -(u - b) = b by abel])
        _ ≤ C * (A.kFunctional (2 ^ (n : ℝ)) u + (A.norm0 (u - b) + 2 ^ (m : ℝ) * A.norm1 b)) := by
            rw [kFunctional_neg hA.norm0_neg hA.norm1_neg]
            gcongr
            exact (kFunctional_le_norm0 hA.norm1_zero _).trans le_self_add
        _ = _ := by ring
  have h₂ := kSumBelow_le (A := A) (θ := θ) (u := u) (v := b) (a := 0) (m := m)
    (X := A.norm0 (u - b) + 2 ^ (m : ℝ) * A.norm1 b) fun n _ => by
      rw [zero_mul, zero_add]
      exact kFunctional_le_two_rpow_sub_mul hA.norm0_zero n m u b
  calc A.discreteKMethodNorm θ 1 q b ≤ A.kSumAbove θ b m + A.kSumBelow θ b m :=
        discreteKMethodNorm_le_kSumAbove_add_kSumBelow hq m _
    _ ≤ _ := add_le_add h₁ h₂
    _ = _ := by rw [holmstedtSideConst, sub_sub_cancel]; ring

/-- The constant `C + holmstedtSideConst C θ₀ + holmstedtSideConst C (1 - θ₁)` of Holmstedt's
formula for the couple of K-spaces. -/
noncomputable def holmstedtConst (C : ℝ≥0∞) (θ₀ θ₁ : ℝ) : ℝ≥0∞ :=
  C + (holmstedtSideConst C θ₀ + holmstedtSideConst C (1 - θ₁))

/-- The constant `holmstedtConst C θ₀ θ₁` is finite for `C < ∞` and `0 < θ₀, θ₁ < 1`. -/
theorem holmstedtConst_ne_top (hC : C ≠ ∞) (hθ₀ : 0 < θ₀) (hθ₀' : θ₀ < 1) (hθ₁ : 0 < θ₁)
    (hθ₁' : θ₁ < 1) : holmstedtConst C θ₀ θ₁ ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨hC, ENNReal.add_ne_top.2 ⟨holmstedtSideConst_ne_top hC hθ₀ hθ₀',
    holmstedtSideConst_ne_top hC (sub_pos.2 hθ₁') (by linarith)⟩⟩

/-- The term `2^(-mθ) K(2^m, u)` is at most `S₁(m)`, being its first term. -/
theorem two_rpow_mul_kFunctional_le_kSumAbove (u : U) (m : ℤ) :
    2 ^ (-((m : ℝ) * θ)) * A.kFunctional (2 ^ (m : ℝ)) u ≤ A.kSumAbove θ u m :=
  calc 2 ^ (-((m : ℝ) * θ)) * A.kFunctional (2 ^ (m : ℝ)) u
      = A.discreteKSeq θ 1 u (m + ((0 : ℕ) : ℤ)) := by
        rw [Nat.cast_zero, add_zero, discreteKSeq_one]
    _ ≤ A.kSumAbove θ u m := le_tsum (f := fun j : ℕ => A.discreteKSeq θ 1 u (m + j)) 0

/-- **Holmstedt's formula, the upper bound in `ℓ₁` form** (Holmstedt 1970; Bergh–Löfström,
Theorem 3.6.1, in discrete form, with `ℓ₁` sums in place of the `ℓ_{q_i}` norms of
Theorem 3.6.1, which is enough for the reiteration theorem): for a couple quasi-normed with
constant `C`, `q₀, q₁ ≥ 1`, `0 < θ₀, θ₁ < 1`, `m ∈ ℤ` and `s = 2^(m(θ₁-θ₀))`, the K-functional
of the couple of K-spaces satisfies `KBar(s, u) ≤ holmstedtConst C θ₀ θ₁ · (S₀(m) + s S₁(m))`,
with `S₀(m) = ∑_{n < m} 2^(-nθ₀) K(2^n, u)` and `S₁(m) = ∑_{n ≥ m} 2^(-nθ₁) K(2^n, u)`. -/
theorem kFunctional_kCouple_le (hA : A.IsQuasiNormed C) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁)
    (hθ₀ : 0 < θ₀) (hθ₀' : θ₀ < 1) (hθ₁ : 0 < θ₁) (hθ₁' : θ₁ < 1) (m : ℤ) (u : U) :
    (A.kCouple θ₀ q₀ θ₁ q₁).kFunctional (2 ^ ((m : ℝ) * (θ₁ - θ₀))) u ≤
      holmstedtConst C θ₀ θ₁ *
        (A.kSumBelow θ₀ u m + 2 ^ ((m : ℝ) * (θ₁ - θ₀)) * A.kSumAbove θ₁ u m) := by
  set G := holmstedtSideConst C θ₀ + holmstedtSideConst C (1 - θ₁) with hG
  have hGt : G ≠ ∞ := ENNReal.add_ne_top.2 ⟨holmstedtSideConst_ne_top hA.ne_top hθ₀ hθ₀',
    holmstedtSideConst_ne_top hA.ne_top (sub_pos.2 hθ₁') (by linarith)⟩
  have hs : (2 : ℝ≥0∞) ^ ((m : ℝ) * (θ₁ - θ₀)) * 2 ^ (-((m : ℝ) * θ₁)) = 2 ^ (-((m : ℝ) * θ₀)) := by
    rw [two_rpow_mul_two_rpow]; congr 1; ring
  have hK : 2 ^ (-((m : ℝ) * θ₀)) * A.kFunctional (2 ^ (m : ℝ)) u ≤
      2 ^ ((m : ℝ) * (θ₁ - θ₀)) * A.kSumAbove θ₁ u m := by
    rw [← hs, mul_assoc]
    gcongr
    exact two_rpow_mul_kFunctional_le_kSumAbove u m
  have hstep : (A.kCouple θ₀ q₀ θ₁ q₁).kFunctional (2 ^ ((m : ℝ) * (θ₁ - θ₀))) u ≤
      (C * A.kSumBelow θ₀ u m + 2 ^ ((m : ℝ) * (θ₁ - θ₀)) * (C * A.kSumAbove θ₁ u m)) +
        G * 2 ^ (-((m : ℝ) * θ₀)) * A.kFunctional (2 ^ (m : ℝ)) u := by
    refine le_add_mul_kFunctional (A := A)
      (ENNReal.mul_ne_top hGt (ENNReal.two_rpow_ne_top _)) fun b => ?_
    calc (A.kCouple θ₀ q₀ θ₁ q₁).kFunctional (2 ^ ((m : ℝ) * (θ₁ - θ₀))) u
        ≤ A.discreteKMethodNorm θ₀ 1 q₀ (u - b) +
            2 ^ ((m : ℝ) * (θ₁ - θ₀)) * A.discreteKMethodNorm θ₁ 1 q₁ b :=
          kFunctional_le (A := A.kCouple θ₀ q₀ θ₁ q₁) b u
      _ ≤ (C * A.kSumBelow θ₀ u m + 2 ^ (-((m : ℝ) * θ₀)) * holmstedtSideConst C θ₀ *
            (A.norm0 (u - b) + 2 ^ (m : ℝ) * A.norm1 b)) + 2 ^ ((m : ℝ) * (θ₁ - θ₀)) *
            (C * A.kSumAbove θ₁ u m + 2 ^ (-((m : ℝ) * θ₁)) * holmstedtSideConst C (1 - θ₁) *
            (A.norm0 (u - b) + 2 ^ (m : ℝ) * A.norm1 b)) := by
          gcongr
          · exact discreteKMethodNorm_sub_le_kSumBelow hA hq₀ m u b
          · exact discreteKMethodNorm_le_kSumAbove hA hq₁ m u b
      _ = _ := by rw [← hs, hG]; ring
  calc (A.kCouple θ₀ q₀ θ₁ q₁).kFunctional (2 ^ ((m : ℝ) * (θ₁ - θ₀))) u
      ≤ (C * A.kSumBelow θ₀ u m + 2 ^ ((m : ℝ) * (θ₁ - θ₀)) * (C * A.kSumAbove θ₁ u m)) +
          G * (2 ^ ((m : ℝ) * (θ₁ - θ₀)) * A.kSumAbove θ₁ u m) := by
        refine hstep.trans ?_
        rw [mul_assoc G]
        gcongr
    _ = C * A.kSumBelow θ₀ u m + (C + G) * (2 ^ ((m : ℝ) * (θ₁ - θ₀)) * A.kSumAbove θ₁ u m) := by
        ring
    _ ≤ (C + G) * A.kSumBelow θ₀ u m +
          (C + G) * (2 ^ ((m : ℝ) * (θ₁ - θ₀)) * A.kSumAbove θ₁ u m) := by
        gcongr
        exact le_self_add
    _ = _ := by rw [holmstedtConst, ← hG, mul_add]

/-- The constant `C + (1 + holmstedtSideConst C (1 - θ₁))` of Holmstedt's formula for the left
endpoint couple. -/
noncomputable def endpointHolmstedtConst (C : ℝ≥0∞) (θ₁ : ℝ) : ℝ≥0∞ :=
  C + (1 + holmstedtSideConst C (1 - θ₁))

/-- The constant `endpointHolmstedtConst C θ₁` is finite for `C < ∞` and `0 < θ₁ < 1`. -/
theorem endpointHolmstedtConst_ne_top (hC : C ≠ ∞) (hθ₁ : 0 < θ₁) (hθ₁' : θ₁ < 1) :
    endpointHolmstedtConst C θ₁ ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨hC, ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    holmstedtSideConst_ne_top hC (sub_pos.2 hθ₁') (by linarith)⟩⟩

/-- **Holmstedt's formula for the left endpoint couple**, the upper bound in `ℓ₁` form (with an
`ℓ₁` sum in place of the `ℓ_{q₁}` norm of Bergh–Löfström, Theorem 3.6.1, which is enough for
the reiteration theorem): for a couple quasi-normed with constant `C`, `q₁ ≥ 1`, `0 < θ₁ < 1`,
`m ∈ ℤ` and `s = 2^(mθ₁)`, the K-functional of `(N₀, ‖·‖_{θ₁,q₁})` satisfies
`KBar(s, u) ≤ endpointHolmstedtConst C θ₁ · s S₁(m)`, with
`S₁(m) = ∑_{n ≥ m} 2^(-nθ₁) K(2^n, u)`. -/
theorem kFunctional_leftKCouple_le (hA : A.IsQuasiNormed C) (hq₁ : 1 ≤ q₁) (hθ₁ : 0 < θ₁)
    (hθ₁' : θ₁ < 1) (m : ℤ) (u : U) :
    (A.leftKCouple θ₁ q₁).kFunctional (2 ^ ((m : ℝ) * θ₁)) u ≤
      endpointHolmstedtConst C θ₁ * (2 ^ ((m : ℝ) * θ₁) * A.kSumAbove θ₁ u m) := by
  set G := 1 + holmstedtSideConst C (1 - θ₁) with hG
  have hGt : G ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    holmstedtSideConst_ne_top hA.ne_top (sub_pos.2 hθ₁') (by linarith)⟩
  have hs : (2 : ℝ≥0∞) ^ ((m : ℝ) * θ₁) * 2 ^ (-((m : ℝ) * θ₁)) = 1 := by
    rw [two_rpow_mul_two_rpow, add_neg_cancel, ENNReal.rpow_zero]
  have hK : A.kFunctional (2 ^ (m : ℝ)) u ≤ 2 ^ ((m : ℝ) * θ₁) * A.kSumAbove θ₁ u m := by
    calc A.kFunctional (2 ^ (m : ℝ)) u
        = 2 ^ ((m : ℝ) * θ₁) * (2 ^ (-((m : ℝ) * θ₁)) * A.kFunctional (2 ^ (m : ℝ)) u) := by
          rw [← mul_assoc, hs, one_mul]
      _ ≤ _ := by gcongr; exact two_rpow_mul_kFunctional_le_kSumAbove u m
  have hstep : (A.leftKCouple θ₁ q₁).kFunctional (2 ^ ((m : ℝ) * θ₁)) u ≤
      2 ^ ((m : ℝ) * θ₁) * (C * A.kSumAbove θ₁ u m) + G * A.kFunctional (2 ^ (m : ℝ)) u := by
    refine le_add_mul_kFunctional hGt fun b => ?_
    calc (A.leftKCouple θ₁ q₁).kFunctional (2 ^ ((m : ℝ) * θ₁)) u
        ≤ A.norm0 (u - b) + 2 ^ ((m : ℝ) * θ₁) * A.discreteKMethodNorm θ₁ 1 q₁ b :=
          kFunctional_le (A := A.leftKCouple θ₁ q₁) b u
      _ ≤ (A.norm0 (u - b) + 2 ^ (m : ℝ) * A.norm1 b) + 2 ^ ((m : ℝ) * θ₁) *
            (C * A.kSumAbove θ₁ u m + 2 ^ (-((m : ℝ) * θ₁)) * holmstedtSideConst C (1 - θ₁) *
            (A.norm0 (u - b) + 2 ^ (m : ℝ) * A.norm1 b)) := by
          gcongr
          · exact le_self_add
          · exact discreteKMethodNorm_le_kSumAbove hA hq₁ m u b
      _ = 2 ^ ((m : ℝ) * θ₁) * (C * A.kSumAbove θ₁ u m) + (1 + (2 ^ ((m : ℝ) * θ₁) *
            2 ^ (-((m : ℝ) * θ₁))) * holmstedtSideConst C (1 - θ₁)) *
            (A.norm0 (u - b) + 2 ^ (m : ℝ) * A.norm1 b) := by ring
      _ = _ := by rw [hs, one_mul]
  calc (A.leftKCouple θ₁ q₁).kFunctional (2 ^ ((m : ℝ) * θ₁)) u
      ≤ 2 ^ ((m : ℝ) * θ₁) * (C * A.kSumAbove θ₁ u m) +
          G * (2 ^ ((m : ℝ) * θ₁) * A.kSumAbove θ₁ u m) := hstep.trans (by gcongr)
    _ = _ := by rw [endpointHolmstedtConst, ← hG]; ring

/-- **Swapping turns the sum from `-m` on into the sum up to `m`**: `S₁(-m)` of the swapped
couple with exponent `1 - θ₀` is `S₀(m + 1) = ∑_{n ≤ m} 2^(-nθ₀) K(2^n, u)` of `A`, by
`discreteKSeq_swap`. -/
theorem kSumAbove_swap (u : U) (m : ℤ) :
    A.swap.kSumAbove (1 - θ₀) u (-m) = A.kSumBelow θ₀ u (m + 1) := by
  rw [kSumAbove, kSumBelow]
  congr 1
  funext j
  rw [discreteKSeq_swap, sub_sub_cancel]
  congr 1
  ring

/-- **Holmstedt's formula for the right endpoint couple**, the upper bound in `ℓ₁` form: for a
couple quasi-normed with constant `C`, `q₀ ≥ 1`, `0 < θ₀ < 1` and `m ∈ ℤ`, the K-functional of
`(‖·‖_{θ₀,q₀}, N₁)` satisfies
`KBar(2^(m(1-θ₀)), u) ≤ endpointHolmstedtConst C (1 - θ₀) · ∑_{n ≤ m} 2^(-nθ₀) K(2^n, u)`, the sum
being `S₀(m + 1)`.  It is `kFunctional_leftKCouple_le` for the swapped couple
(`rightKCouple_eq_swap`, `kFunctional_swap`). -/
theorem kFunctional_rightKCouple_le (hA : A.IsQuasiNormed C) (hq₀ : 1 ≤ q₀) (hθ₀ : 0 < θ₀)
    (hθ₀' : θ₀ < 1) (m : ℤ) (u : U) :
    (A.rightKCouple θ₀ q₀).kFunctional (2 ^ ((m : ℝ) * (1 - θ₀))) u ≤
      endpointHolmstedtConst C (1 - θ₀) * A.kSumBelow θ₀ u (m + 1) := by
  have h0 : (2 : ℝ≥0∞) ^ ((m : ℝ) * (1 - θ₀)) ≠ 0 :=
    (ENNReal.rpow_pos two_pos ENNReal.ofNat_ne_top).ne'
  have ht : (2 : ℝ≥0∞) ^ ((m : ℝ) * (1 - θ₀)) ≠ ∞ := ENNReal.two_rpow_ne_top _
  have hK := kFunctional_leftKCouple_le (A := A.swap) (q₁ := q₀) hA.swap hq₀ (sub_pos.2 hθ₀')
    (by linarith) (-m) u
  have e : -((m : ℝ) * (1 - θ₀)) = ((-m : ℤ) : ℝ) * (1 - θ₀) := by push_cast; ring
  have hs : (2 : ℝ≥0∞) ^ ((m : ℝ) * (1 - θ₀)) * 2 ^ (((-m : ℤ) : ℝ) * (1 - θ₀)) = 1 := by
    rw [← e, two_rpow_mul_two_rpow, add_neg_cancel, ENNReal.rpow_zero]
  rw [rightKCouple_eq_swap, kFunctional_swap h0 ht, ← ENNReal.rpow_neg, e]
  calc 2 ^ ((m : ℝ) * (1 - θ₀)) *
        (A.swap.leftKCouple (1 - θ₀) q₀).kFunctional (2 ^ (((-m : ℤ) : ℝ) * (1 - θ₀))) u
      ≤ 2 ^ ((m : ℝ) * (1 - θ₀)) * (endpointHolmstedtConst C (1 - θ₀) *
          (2 ^ (((-m : ℤ) : ℝ) * (1 - θ₀)) * A.swap.kSumAbove (1 - θ₀) u (-m))) := by
        gcongr
    _ = endpointHolmstedtConst C (1 - θ₀) * ((2 ^ ((m : ℝ) * (1 - θ₀)) *
          2 ^ (((-m : ℤ) : ℝ) * (1 - θ₀))) * A.swap.kSumAbove (1 - θ₀) u (-m)) := by ring
    _ = _ := by rw [hs, one_mul, kSumAbove_swap]

/-! ### The reiteration theorem -/

/-- The weighted sum below `m` as a geometric convolution: for `θ = θ₀ + ηρ`,
`2^(-mρη) S₀(m) = ∑_{j ≥ 0} 2^(-(j+1)ηρ) c_{m-(j+1)}` with `c_n = 2^(-nθ) K(2^n, u)`. -/
theorem two_rpow_mul_kSumBelow (hθ : θ = θ₀ + η * ρ) (m : ℤ) (u : U) :
    2 ^ (-((m : ℝ) * ρ * η)) * A.kSumBelow θ₀ u m =
      ∑' j : ℕ, dyadicWeight (-(η * ρ)) (j + 1) * A.discreteKSeq θ 1 u (m - (j + 1)) := by
  rw [kSumBelow, ← ENNReal.tsum_mul_left]
  congr 1
  funext j
  rw [discreteKSeq_one, discreteKSeq_one, dyadicWeight, ← mul_assoc, ← mul_assoc,
    two_rpow_mul_two_rpow, two_rpow_mul_two_rpow, hθ]
  congr 2
  push_cast
  ring

/-- The weighted sum from `m` on as a geometric convolution: for `θ₁ = θ + (1 - η) ρ`,
`2^(-mρη) 2^(mρ) S₁(m) = ∑_{j ≥ 0} 2^(-j(1-η)ρ) c_{m+j}` with `c_n = 2^(-nθ) K(2^n, u)`. -/
theorem two_rpow_mul_kSumAbove (hθ : θ₁ = θ + (1 - η) * ρ) (m : ℤ) (u : U) :
    2 ^ (-((m : ℝ) * ρ * η)) * (2 ^ ((m : ℝ) * ρ) * A.kSumAbove θ₁ u m) =
      ∑' j : ℕ, dyadicWeight (-((1 - η) * ρ)) j * A.discreteKSeq θ 1 u (m + j) := by
  rw [kSumAbove, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  congr 1
  funext j
  rw [discreteKSeq_one, discreteKSeq_one, dyadicWeight, ← mul_assoc, ← mul_assoc, ← mul_assoc,
    two_rpow_mul_two_rpow, two_rpow_mul_two_rpow, two_rpow_mul_two_rpow, hθ]
  congr 2
  push_cast
  ring

/-- The constant
`holmstedtConst C θ₀ θ₁ · ((1 - 2^(-η(θ₁-θ₀)))⁻¹ + (1 - 2^(-(1-η)(θ₁-θ₀)))⁻¹)` of the
reiteration theorem. -/
noncomputable def reiterationConst (C : ℝ≥0∞) (θ₀ θ₁ η : ℝ) : ℝ≥0∞ :=
  holmstedtConst C θ₀ θ₁ * ((1 - (2 : ℝ≥0∞) ^ (-(η * (θ₁ - θ₀))))⁻¹ +
    (1 - (2 : ℝ≥0∞) ^ (-((1 - η) * (θ₁ - θ₀))))⁻¹)

/-- The constant `reiterationConst C θ₀ θ₁ η` is finite for `C < ∞`, `0 < θ₀ < θ₁ < 1` and
`0 < η < 1`. -/
theorem reiterationConst_ne_top (hC : C ≠ ∞) (hθ₀ : 0 < θ₀) (hθ : θ₀ < θ₁) (hθ₁ : θ₁ < 1)
    (hη : 0 < η) (hη' : η < 1) : reiterationConst C θ₀ θ₁ η ≠ ∞ :=
  ENNReal.mul_ne_top (holmstedtConst_ne_top hC hθ₀ (hθ.trans hθ₁) (hθ₀.trans hθ) hθ₁)
    (ENNReal.add_ne_top.2 ⟨ENNReal.one_sub_two_rpow_neg_inv_ne_top
      (mul_pos hη (sub_pos.2 hθ)),
      ENNReal.one_sub_two_rpow_neg_inv_ne_top (mul_pos (sub_pos.2 hη') (sub_pos.2 hθ))⟩)

/-- **The discrete reiteration bound**, via the Holmstedt estimate above. For a couple
quasi-normed with constant `C`, `q₀, q₁, q ≥ 1`, `0 < θ₀, θ₁ < 1` and
`θ = (1 - η) θ₀ + η θ₁`, the discrete K-norm of the couple of K-spaces on the grid
`t = 2^(n(θ₁-θ₀))` satisfies `‖u‖_{η,q} ≤ reiterationConst C θ₀ θ₁ η · ‖u‖_{θ,q}`. -/
theorem kCouple_discreteKMethodNorm_le (hA : A.IsQuasiNormed C) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁)
    (hq : 1 ≤ q) (hθ₀ : 0 < θ₀) (hθ₀' : θ₀ < 1) (hθ₁ : 0 < θ₁) (hθ₁' : θ₁ < 1) (η : ℝ) (u : U) :
    (A.kCouple θ₀ q₀ θ₁ q₁).discreteKMethodNorm η (θ₁ - θ₀) q u ≤
      reiterationConst C θ₀ θ₁ η * A.discreteKMethodNorm ((1 - η) * θ₀ + η * θ₁) 1 q u := by
  set c := A.discreteKSeq ((1 - η) * θ₀ + η * θ₁) 1 u
  set x : ℤ → ℝ≥0∞ := fun m =>
    ∑' j : ℕ, dyadicWeight (-(η * (θ₁ - θ₀))) (j + 1) * c (m - (j + 1))
  set y : ℤ → ℝ≥0∞ := fun m => ∑' j : ℕ, dyadicWeight (-((1 - η) * (θ₁ - θ₀))) j * c (m + j)
  have hterm : ∀ m, (A.kCouple θ₀ q₀ θ₁ q₁).discreteKSeq η (θ₁ - θ₀) u m ≤
      holmstedtConst C θ₀ θ₁ * (x m + y m) := fun m => by
    rw [discreteKSeq]
    calc 2 ^ (-((m : ℝ) * (θ₁ - θ₀) * η)) *
          (A.kCouple θ₀ q₀ θ₁ q₁).kFunctional (2 ^ ((m : ℝ) * (θ₁ - θ₀))) u
        ≤ 2 ^ (-((m : ℝ) * (θ₁ - θ₀) * η)) * (holmstedtConst C θ₀ θ₁ *
            (A.kSumBelow θ₀ u m + 2 ^ ((m : ℝ) * (θ₁ - θ₀)) * A.kSumAbove θ₁ u m)) := by
          gcongr
          exact kFunctional_kCouple_le hA hq₀ hq₁ hθ₀ hθ₀' hθ₁ hθ₁' m u
      _ = holmstedtConst C θ₀ θ₁ * (2 ^ (-((m : ℝ) * (θ₁ - θ₀) * η)) * A.kSumBelow θ₀ u m +
            2 ^ (-((m : ℝ) * (θ₁ - θ₀) * η)) *
              (2 ^ ((m : ℝ) * (θ₁ - θ₀)) * A.kSumAbove θ₁ u m)) := by ring
      _ = _ := by
          rw [two_rpow_mul_kSumBelow (θ := (1 - η) * θ₀ + η * θ₁) (θ₀ := θ₀) (η := η)
            (ρ := θ₁ - θ₀) (by ring), two_rpow_mul_kSumAbove (θ := (1 - η) * θ₀ + η * θ₁)
            (θ₁ := θ₁) (η := η) (ρ := θ₁ - θ₀) (by ring)]
  calc (A.kCouple θ₀ q₀ θ₁ q₁).discreteKMethodNorm η (θ₁ - θ₀) q u
      ≤ lqNorm q (fun m => holmstedtConst C θ₀ θ₁ * (x m + y m)) := ENNReal.lqNorm_mono hterm
    _ ≤ holmstedtConst C θ₀ θ₁ * (lqNorm q x + lqNorm q y) := by
        rw [ENNReal.lqNorm_const_mul]
        gcongr
        exact ENNReal.lqNorm_add_le hq _ _
    _ ≤ holmstedtConst C θ₀ θ₁ * ((1 - (2 : ℝ≥0∞) ^ (-(η * (θ₁ - θ₀))))⁻¹ * lqNorm q c +
          (1 - (2 : ℝ≥0∞) ^ (-((1 - η) * (θ₁ - θ₀))))⁻¹ * lqNorm q c) := by
        gcongr
        · exact ENNReal.lqNorm_tsum_geom_sub_le hq _ c
        · exact ENNReal.lqNorm_tsum_geom_add_le hq _ c
    _ = _ := by rw [reiterationConst, discreteKMethodNorm]; ring

/-- The constant `endpointHolmstedtConst C θ₁ · (1 - 2^(-(1-η)θ₁))⁻¹` of the reiteration theorem
for the endpoint couples. -/
noncomputable def endpointReiterationConst (C : ℝ≥0∞) (θ₁ η : ℝ) : ℝ≥0∞ :=
  endpointHolmstedtConst C θ₁ * (1 - (2 : ℝ≥0∞) ^ (-((1 - η) * θ₁)))⁻¹

/-- The constant `endpointReiterationConst C θ₁ η` is finite for `C < ∞`, `0 < θ₁ < 1` and
`η < 1`. -/
theorem endpointReiterationConst_ne_top (hC : C ≠ ∞) (hθ₁ : 0 < θ₁) (hθ₁' : θ₁ < 1)
    (hη' : η < 1) : endpointReiterationConst C θ₁ η ≠ ∞ :=
  ENNReal.mul_ne_top (endpointHolmstedtConst_ne_top hC hθ₁ hθ₁')
    (ENNReal.one_sub_two_rpow_neg_inv_ne_top (mul_pos (sub_pos.2 hη') hθ₁))

/-- **The reiteration bound for the left endpoint couple**: for a couple quasi-normed with
constant `C`, `q₁, q ≥ 1` and `0 < θ₁ < 1`, the discrete K-norm of `(N₀, ‖·‖_{θ₁,q₁})` on the
grid `t = 2^(nθ₁)` satisfies `‖u‖_{η,q} ≤ endpointReiterationConst C θ₁ η · ‖u‖_{ηθ₁,q}`. -/
theorem leftKCouple_discreteKMethodNorm_le (hA : A.IsQuasiNormed C) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q)
    (hθ₁ : 0 < θ₁) (hθ₁' : θ₁ < 1) (η : ℝ) (u : U) :
    (A.leftKCouple θ₁ q₁).discreteKMethodNorm η θ₁ q u ≤
      endpointReiterationConst C θ₁ η * A.discreteKMethodNorm (η * θ₁) 1 q u := by
  set c := A.discreteKSeq (η * θ₁) 1 u
  have hterm : ∀ m, (A.leftKCouple θ₁ q₁).discreteKSeq η θ₁ u m ≤ endpointHolmstedtConst C θ₁ *
      ∑' j : ℕ, dyadicWeight (-((1 - η) * θ₁)) j * c (m + j) := fun m => by
    rw [discreteKSeq, ← two_rpow_mul_kSumAbove (θ := η * θ₁) (θ₁ := θ₁) (η := η) (ρ := θ₁)
      (by ring), mul_left_comm]
    gcongr
    exact kFunctional_leftKCouple_le hA hq₁ hθ₁ hθ₁' m u
  calc (A.leftKCouple θ₁ q₁).discreteKMethodNorm η θ₁ q u
      ≤ lqNorm q (fun m => endpointHolmstedtConst C θ₁ *
          ∑' j : ℕ, dyadicWeight (-((1 - η) * θ₁)) j * c (m + j)) := ENNReal.lqNorm_mono hterm
    _ ≤ endpointHolmstedtConst C θ₁ * ((1 - (2 : ℝ≥0∞) ^ (-((1 - η) * θ₁)))⁻¹ * lqNorm q c) := by
        rw [ENNReal.lqNorm_const_mul]
        gcongr
        exact ENNReal.lqNorm_tsum_geom_add_le hq _ c
    _ = _ := by rw [endpointReiterationConst, discreteKMethodNorm]; ring

/-- **The reiteration bound for the right endpoint couple**: for a couple quasi-normed with
constant `C`, `q₀, q ≥ 1` and `0 < θ₀ < 1`, the discrete K-norm of `(‖·‖_{θ₀,q₀}, N₁)` on the grid
`t = 2^(n(1-θ₀))` satisfies
`‖u‖_{η,q} ≤ endpointReiterationConst C (1 - θ₀) (1 - η) · ‖u‖_{(1-η)θ₀+η,q}`, by swapping the
couple (`rightKCouple_eq_swap`). -/
theorem rightKCouple_discreteKMethodNorm_le (hA : A.IsQuasiNormed C) (hq₀ : 1 ≤ q₀)
    (hq : 1 ≤ q) (hθ₀ : 0 < θ₀) (hθ₀' : θ₀ < 1) (η : ℝ) (u : U) :
    (A.rightKCouple θ₀ q₀).discreteKMethodNorm η (1 - θ₀) q u ≤
      endpointReiterationConst C (1 - θ₀) (1 - η) *
        A.discreteKMethodNorm ((1 - η) * θ₀ + η) 1 q u := by
  have h := leftKCouple_discreteKMethodNorm_le (A := A.swap) hA.swap hq₀ hq (sub_pos.2 hθ₀')
    (by linarith) (1 - η) u
  rw [discreteKMethodNorm_swap] at h
  rw [rightKCouple_eq_swap, discreteKMethodNorm_swap]
  convert h using 3
  ring

/-! ### Membership -/

/-- **Equal spaces from comparable discrete K-norms**: for couples `A`, `B`, finite constants
`c, c'`, `η ≥ 0`, `ρ > 0` and `θ ≥ 0`, if `‖u‖^B_{η,ρ,q} ≤ c ‖u‖^A_{θ,1,q}` and
`‖u‖^A_{θ,1,q} ≤ c' ‖u‖^B_{η,ρ,q}`, then `u ∈ (Y₀, Y₁)_{η,q}` if and only if
`u ∈ (X₀, X₁)_{θ,q}` (`memKMethod_iff_discreteKMethodNorm_lt_top`). -/
theorem memKMethod_iff_of_discreteKMethodNorm_le {B : InterpCouple U} {c c' : ℝ≥0∞}
    (hc : c ≠ ∞) (hc' : c' ≠ ∞) (hη : 0 ≤ η) (hρ : 0 < ρ) (hθ : 0 ≤ θ) {u : U}
    (h : B.discreteKMethodNorm η ρ q u ≤ c * A.discreteKMethodNorm θ 1 q u)
    (h' : A.discreteKMethodNorm θ 1 q u ≤ c' * B.discreteKMethodNorm η ρ q u) :
    B.MemKMethod η q u ↔ A.MemKMethod θ q u := by
  rw [memKMethod_iff_discreteKMethodNorm_lt_top hη hρ,
    memKMethod_iff_discreteKMethodNorm_lt_top (ρ := 1) hθ one_pos]
  exact ⟨fun hB => h'.trans_lt (ENNReal.mul_lt_top hc'.lt_top hB),
    fun hA => h.trans_lt (ENNReal.mul_lt_top hc.lt_top hA)⟩

/-- **Reiteration for discrete K-norms**, a variant of Bergh–Löfström, Theorems 3.5.3 and 3.11.5.
For a couple quasi-normed with constant `C`, `0 < θ₀ < θ₁ < 1`, `0 < η < 1` and `q₀, q₁, q ≥ 1`,
`((X₀, X₁)_{θ₀,q₀}, (X₀, X₁)_{θ₁,q₁})_{η,q} = (X₀, X₁)_{θ,q}` with `θ = (1 - η) θ₀ + η θ₁`, for
the discrete K-norms of the two K-spaces. -/
theorem memKMethod_kCouple_iff (hA : A.IsQuasiNormed C) (hθ₀ : 0 < θ₀) (hθ : θ₀ < θ₁)
    (hθ₁ : θ₁ < 1) (hη : 0 < η) (hη' : η < 1) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q)
    {u : U} :
    (A.kCouple θ₀ q₀ θ₁ q₁).MemKMethod η q u ↔ A.MemKMethod ((1 - η) * θ₀ + η * θ₁) q u :=
  memKMethod_iff_of_discreteKMethodNorm_le (reiterationConst_ne_top hA.ne_top hθ₀ hθ hθ₁ hη hη')
    hA.ne_top hη.le (sub_pos.2 hθ) (by nlinarith)
    (kCouple_discreteKMethodNorm_le hA hq₀ hq₁ hq hθ₀ (hθ.trans hθ₁) (hθ₀.trans hθ) hθ₁ η u)
    (discreteKMethodNorm_le_kCouple hA (one_pos.trans_le hq₀).ne'
      (one_pos.trans_le hq₁).ne' η q u)

/-- **Reiteration with the left endpoint space**, including the outer endpoint `η = 0`.
For a couple quasi-normed with constant `C`, `0 < θ₁ < 1`, `0 ≤ η < 1` and `q₁, q ≥ 1`,
`(X₀, (X₀, X₁)_{θ₁,q₁})_{η,q} = (X₀, X₁)_{ηθ₁,q}`. -/
theorem memKMethod_leftKCouple_iff (hA : A.IsQuasiNormed C) (hθ₁ : 0 < θ₁) (hθ₁' : θ₁ < 1)
    (hη : 0 ≤ η) (hη' : η < 1) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) {u : U} :
    (A.leftKCouple θ₁ q₁).MemKMethod η q u ↔ A.MemKMethod (η * θ₁) q u :=
  memKMethod_iff_of_discreteKMethodNorm_le
    (endpointReiterationConst_ne_top hA.ne_top hθ₁ hθ₁' hη') hA.ne_top hη hθ₁
    (mul_nonneg hη hθ₁.le) (leftKCouple_discreteKMethodNorm_le hA hq₁ hq hθ₁ hθ₁' η u)
    (discreteKMethodNorm_le_leftKCouple hA (one_pos.trans_le hq₁).ne' η q u)

/-- **Reiteration with the right endpoint space**, including the outer endpoint `η = 1`.
For a couple quasi-normed with constant `C`, `0 < θ₀ < 1`, `η > 0` and `q₀, q ≥ 1`,
`((X₀, X₁)_{θ₀,q₀}, X₁)_{η,q} = (X₀, X₁)_{(1-η)θ₀+η,q}`. -/
theorem memKMethod_rightKCouple_iff (hA : A.IsQuasiNormed C) (hθ₀ : 0 < θ₀) (hθ₀' : θ₀ < 1)
    (hη : 0 < η) (hq₀ : 1 ≤ q₀) (hq : 1 ≤ q) {u : U} :
    (A.rightKCouple θ₀ q₀).MemKMethod η q u ↔ A.MemKMethod ((1 - η) * θ₀ + η) q u :=
  memKMethod_iff_of_discreteKMethodNorm_le
    (endpointReiterationConst_ne_top hA.ne_top (sub_pos.2 hθ₀') (by linarith) (by linarith))
    hA.ne_top hη.le (sub_pos.2 hθ₀') (by nlinarith)
    (rightKCouple_discreteKMethodNorm_le hA hq₀ hq hθ₀ hθ₀' η u)
    (discreteKMethodNorm_le_rightKCouple hA (one_pos.trans_le hq₀).ne' η q u)

/-- **The reiteration theorem for the continuous K-norms**: under the hypotheses of
`memKMethod_kCouple_iff`, `((X₀, X₁)_{θ₀,q₀}, (X₀, X₁)_{θ₁,q₁})_{η,q} = (X₀, X₁)_{θ,q}` with
`θ = (1 - η) θ₀ + η θ₁`, for the continuous K-norms `‖·‖_{K,θ_i,q_i}` of the two K-spaces. -/
theorem memKMethod_kMethodCouple_iff (hA : A.IsQuasiNormed C) (hθ₀ : 0 < θ₀) (hθ : θ₀ < θ₁)
    (hθ₁ : θ₁ < 1) (hη : 0 < η) (hη' : η < 1) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q)
    {u : U} :
    (A.kMethodCouple θ₀ q₀ θ₁ q₁).MemKMethod η q u ↔
      A.MemKMethod ((1 - η) * θ₀ + η * θ₁) q u := by
  rw [← memKMethod_kCouple_iff hA hθ₀ hθ hθ₁ hη hη' hq₀ hq₁ hq]
  exact memKMethod_congr (ApproximationScheme.inv_log_two_rpow_mul_two_rpow_ne_top θ₀ q₀)
    (ApproximationScheme.inv_log_two_rpow_mul_two_rpow_ne_top θ₁ q₁)
    (ApproximationScheme.log_two_rpow_mul_two_rpow_ne_top θ₀ q₀)
    (ApproximationScheme.log_two_rpow_mul_two_rpow_ne_top θ₁ q₁)
    (discreteKMethodNorm_le_mul_kMethodNorm hθ₀.le)
    (discreteKMethodNorm_le_mul_kMethodNorm (hθ₀.trans hθ).le)
    (kMethodNorm_le_mul_discreteKMethodNorm hθ₀.le)
    (kMethodNorm_le_mul_discreteKMethodNorm (hθ₀.trans hθ).le)

end InterpCouple

/-! ### Couples of bounded linear maps -/

namespace ApproximationScheme

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] {ι : Y →L[ℝ] X} {θ₀ θ₁ η : ℝ} {q₀ q₁ q : ℝ≥0∞}

/-- **The reiteration theorem for a bounded linear map** `ι : Y → X`: for `0 < θ₀ < θ₁ < 1`,
`0 < η < 1` and `q₀, q₁, q ≥ 1`, `((X, Y)_{θ₀,q₀}, (X, Y)_{θ₁,q₁})_{η,q} = (X, Y)_{θ,q}` with
`θ = (1 - η) θ₀ + η θ₁`, for the continuous K-norms of
`ApproximationSpaces.Interpolation.KMethod`. -/
theorem memKMethod_reiteration (hθ₀ : 0 < θ₀) (hθ : θ₀ < θ₁) (hθ₁ : θ₁ < 1) (hη : 0 < η)
    (hη' : η < 1) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) {f : X} :
    (⟨kMethodNorm ι θ₀ q₀, kMethodNorm ι θ₁ q₁⟩ : InterpCouple X).MemKMethod η q f ↔
      MemKMethod ι ((1 - η) * θ₀ + η * θ₁) q f := by
  have e : (⟨kMethodNorm ι θ₀ q₀, kMethodNorm ι θ₁ q₁⟩ : InterpCouple X) =
      (InterpCouple.ofMap ι).kMethodCouple θ₀ q₀ θ₁ q₁ := by
    have h₀ : kMethodNorm ι θ₀ q₀ = (InterpCouple.ofMap ι).kMethodNorm θ₀ q₀ :=
      funext fun f => (InterpCouple.kMethodNorm_ofMap f).symm
    have h₁ : kMethodNorm ι θ₁ q₁ = (InterpCouple.ofMap ι).kMethodNorm θ₁ q₁ :=
      funext fun f => (InterpCouple.kMethodNorm_ofMap f).symm
    rw [h₀, h₁]
    rfl
  rw [e, InterpCouple.memKMethod_kMethodCouple_iff InterpCouple.isQuasiNormed_ofMap hθ₀ hθ hθ₁
    hη hη' hq₀ hq₁ hq, InterpCouple.memKMethod_ofMap_iff]

end ApproximationScheme
