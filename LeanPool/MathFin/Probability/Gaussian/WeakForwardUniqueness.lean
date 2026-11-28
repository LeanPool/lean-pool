/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Weak uniqueness for the constant-coefficient forward equation

`IsWeakForwardFlow afn bfn T ρ` says that a flow of probability measures `ρ : ℝ → Measure ℝ`
solves, on `[0, T]`, the integrated weak forward equation with coefficient functions `afn`,
`bfn : ℝ → ℝ → ℝ`: for every test `g` whose first three derivatives are bounded,

`∫ g dρ s = ∫ g dρ 0 + ∫ x in 0..s, (∫ g' · afn x dρ x + ½ ∫ g'' · bfn x dρ x)`,

and the generator integrand is interval-integrable (so the interval integral is not a junk
value). This is the hypothesis that `MathFin.GyongyMimicry.gyongy_mimicry_gated` states for
the two flows its flow-uniqueness hypothesis `hgate` compares.

`weakForwardUniqueConst` is the constant-coefficient case (`afn ≡ b`, `bfn ≡ v`): two such
flows with `ρ 0 = η 0` coincide on `(0, T]`. It is the statement `hgate` asks for, proved
for constant coefficients. The proof pairs both flows against `cos(ξ·)` and `sin(ξ·)`; the
pairing differences solve a linear system with zero initial value, which Grönwall's
inequality forces to vanish, so the flows have equal characteristic functions
(`MeasureTheory.Measure.ext_of_charFun`).

## Main definitions

* `IsWeakForwardFlow`: a flow of probability measures `ρ` solves, on `[0, T]`, the integrated
  weak forward equation with coefficient functions `afn`, `bfn`, tested against `g` with
  bounded first three derivatives, with interval-integrable generator integrand.

## Main results

* `weakForwardUniqueConst`: two flows solving `IsWeakForwardFlow` with the same constant
  coefficients `b` and `v` and the same initial law coincide at every time `s ∈ (0, T]`.

## References

* [I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*][KaratzasShreve1991]
* [Stroock and Varadhan, *Multidimensional Diffusion Processes*][StroockVaradhan1979]

## Tags

Fokker–Planck equation, weak forward equation, uniqueness of flows, Gyöngy mimicking,
characteristic function, Grönwall inequality, MSC 60J60, MSC 60E10, MSC 35K10
-/

@[expose] public section

namespace MathFin

open MeasureTheory

/-- `ρ` is a flow of probability measures solving, on `[0, T]`, the integrated weak forward
equation with coefficient functions `afn`, `bfn`, for every test `g` with `HasDerivAt` chain
`g, g', g'', g'''` and bounded `g', g'', g'''`. The generator integrand is required to be
interval-integrable, so the interval integral in the identity is a genuine one. -/
def IsWeakForwardFlow (afn bfn : ℝ → ℝ → ℝ) (T : ℝ) (ρ : ℝ → Measure ℝ) : Prop :=
  (∀ s, IsProbabilityMeasure (ρ s)) ∧
  ∀ (g g' g'' g''' : ℝ → ℝ) (C1 C2 C3 : ℝ),
    (∀ x, HasDerivAt g (g' x) x) → (∀ x, HasDerivAt g' (g'' x) x) →
    (∀ x, HasDerivAt g'' (g''' x) x) →
    (∀ x, |g' x| ≤ C1) → (∀ x, |g'' x| ≤ C2) → (∀ x, |g''' x| ≤ C3) →
    ∀ s ∈ Set.Ioc 0 T,
      (∫ y, g y ∂(ρ s) = ∫ y, g y ∂(ρ 0)
        + ∫ x in (0)..s,
          ((∫ y, g' y * afn x y ∂(ρ x)) + 1 / 2 * (∫ y, g'' y * bfn x y ∂(ρ x)))) ∧
      IntervalIntegrable
        (fun x => (∫ y, g' y * afn x y ∂(ρ x)) + 1 / 2 * (∫ y, g'' y * bfn x y ∂(ρ x)))
        volume 0 s

/-- The constant-coefficient identity of `IsWeakForwardFlow`, with the constants pulled out
of the pairings. -/
private lemma IsWeakForwardFlow.const_identity {b v T : ℝ} {ρ : ℝ → Measure ℝ}
    (hρ : IsWeakForwardFlow (fun _ _ ↦ b) (fun _ _ ↦ v) T ρ)
    {g g' g'' g''' : ℝ → ℝ} {C1 C2 C3 : ℝ}
    (h1 : ∀ x, HasDerivAt g (g' x) x) (h2 : ∀ x, HasDerivAt g' (g'' x) x)
    (h3 : ∀ x, HasDerivAt g'' (g''' x) x)
    (hb1 : ∀ x, |g' x| ≤ C1) (hb2 : ∀ x, |g'' x| ≤ C2) (hb3 : ∀ x, |g''' x| ≤ C3)
    {s : ℝ} (hs : s ∈ Set.Ioc 0 T) :
    (∫ y, g y ∂(ρ s) = ∫ y, g y ∂(ρ 0)
      + ∫ r in (0)..s, (b * ∫ y, g' y ∂(ρ r) + v / 2 * ∫ y, g'' y ∂(ρ r))) ∧
    IntervalIntegrable
      (fun r => b * ∫ y, g' y ∂(ρ r) + v / 2 * ∫ y, g'' y ∂(ρ r)) volume 0 s := by
  have hw : (fun r => (∫ y, g' y * b ∂(ρ r)) + 1 / 2 * (∫ y, g'' y * v ∂(ρ r)))
      = fun r => b * ∫ y, g' y ∂(ρ r) + v / 2 * ∫ y, g'' y ∂(ρ r) :=
    funext fun r => by rw [integral_mul_const, integral_mul_const]; ring
  simpa only [hw] using hρ.2 g g' g'' g''' C1 C2 C3 h1 h2 h3 hb1 hb2 hb3 s hs

/-! ### The pairing layer

Against a probability measure, the pairing with a bounded function is bounded
by the sup bound; the integrated identity then makes every admissible
pairing Lipschitz-continuous in time. -/

/-- The increment of an admissible pairing over an interval, both endpoints in
`[0, T]`: the difference of pairings is the oriented integral of the pairing
integrand. -/
private lemma pairing_increment {b v T : ℝ} {ρ : ℝ → Measure ℝ}
    (hρ : IsWeakForwardFlow (fun _ _ ↦ b) (fun _ _ ↦ v) T ρ)
    {g g' g'' g''' : ℝ → ℝ} {C1 C2 C3 : ℝ}
    (h1 : ∀ x, HasDerivAt g (g' x) x) (h2 : ∀ x, HasDerivAt g' (g'' x) x)
    (h3 : ∀ x, HasDerivAt g'' (g''' x) x)
    (hb1 : ∀ x, |g' x| ≤ C1) (hb2 : ∀ x, |g'' x| ≤ C2)
    (hb3 : ∀ x, |g''' x| ≤ C3)
    {s₀ s : ℝ} (hs₀ : s₀ ∈ Set.Icc 0 T) (hs : s ∈ Set.Icc 0 T) :
    ∫ y, g y ∂(ρ s) - ∫ y, g y ∂(ρ s₀)
      = ∫ r in s₀..s, (b * ∫ y, g' y ∂(ρ r) + v / 2 * ∫ y, g'' y ∂(ρ r)) := by
  set w : ℝ → ℝ := fun r => b * ∫ y, g' y ∂(ρ r) + v / 2 * ∫ y, g'' y ∂(ρ r)
  have ident : ∀ u ∈ Set.Ioc 0 T,
      ∫ y, g y ∂(ρ u) = ∫ y, g y ∂(ρ 0) + ∫ r in (0)..u, w r ∧
      IntervalIntegrable w volume 0 u := fun u hu =>
    hρ.const_identity h1 h2 h3 hb1 hb2 hb3 hu
  have interior : ∀ {u₁ u₂ : ℝ}, 0 < u₁ → 0 < u₂ → u₁ ≤ T → u₂ ≤ T →
      ∫ y, g y ∂(ρ u₂) - ∫ y, g y ∂(ρ u₁) = ∫ r in u₁..u₂, w r := by
    intro u₁ u₂ hu₁ hu₂ hu₁T hu₂T
    have hI1 := ident u₁ ⟨hu₁, hu₁T⟩
    have hI2 := ident u₂ ⟨hu₂, hu₂T⟩
    rcases le_total u₂ u₁ with hle | hle
    · have hsub : IntervalIntegrable w volume u₂ u₁ := hI1.2.mono_set
        (Set.uIcc_subset_uIcc (Set.mem_uIcc_of_le (le_of_lt hu₂) hle)
          (Set.mem_uIcc_of_le (le_of_lt hu₁) le_rfl))
      have hadd := intervalIntegral.integral_add_adjacent_intervals hI2.2 hsub
      rw [hI2.1, hI1.1, ← hadd, intervalIntegral.integral_symm u₂ u₁]
      ring
    · have hsub : IntervalIntegrable w volume u₁ u₂ := hI2.2.mono_set
        (Set.uIcc_subset_uIcc (Set.mem_uIcc_of_le (le_of_lt hu₁) hle)
          (Set.mem_uIcc_of_le (le_of_lt hu₂) le_rfl))
      have hadd := intervalIntegral.integral_add_adjacent_intervals hI1.2 hsub
      rw [hI2.1, hI1.1, ← hadd]
      ring
  rcases eq_or_lt_of_le hs₀.1 with h0 | h0pos
  · subst h0
    rcases eq_or_lt_of_le hs.1 with h1eq | h1pos
    · subst h1eq; rw [sub_self, intervalIntegral.integral_same]
    · linarith [(ident s ⟨h1pos, hs.2⟩).1]
  · rcases eq_or_lt_of_le hs.1 with h1eq | h1pos
    · subst h1eq
      have hI1 := ident s₀ ⟨h0pos, hs₀.2⟩
      have hsym : (∫ r in s₀..(0:ℝ), w r) = -(∫ r in (0)..s₀, w r) :=
        intervalIntegral.integral_symm 0 s₀
      rw [hI1.1, hsym]
      ring
    · exact interior h0pos h1pos hs₀.2 hs.2

/-- The pairing of an admissible test is Lipschitz in time on `[0, T]`: the
pairing increment is an interval integral of an integrand bounded by
`|b| * C1 + |v| / 2 * C2` (via `norm_integral_le_of_norm_le_const` on each of the two pieces). -/
private lemma abs_pairing_lipschitz {b v T : ℝ} {ρ : ℝ → Measure ℝ}
    (hρ : IsWeakForwardFlow (fun _ _ ↦ b) (fun _ _ ↦ v) T ρ)
    {g g' g'' g''' : ℝ → ℝ} {C1 C2 C3 : ℝ}
    (h1 : ∀ x, HasDerivAt g (g' x) x) (h2 : ∀ x, HasDerivAt g' (g'' x) x)
    (h3 : ∀ x, HasDerivAt g'' (g''' x) x)
    (hb1 : ∀ x, |g' x| ≤ C1) (hb2 : ∀ x, |g'' x| ≤ C2)
    (hb3 : ∀ x, |g''' x| ≤ C3)
    {s₀ s : ℝ} (hs₀ : s₀ ∈ Set.Icc 0 T) (hs : s ∈ Set.Icc 0 T) :
    |∫ y, g y ∂(ρ s) - ∫ y, g y ∂(ρ s₀)| ≤ (|b| * C1 + |v| / 2 * C2) * |s - s₀| := by
  rw [pairing_increment hρ h1 h2 h3 hb1 hb2 hb3 hs₀ hs, ← Real.norm_eq_abs]
  refine intervalIntegral.norm_integral_le_of_norm_le_const (fun r _ => ?_)
  rw [Real.norm_eq_abs]
  have := hρ.1 r
  have hb1' : |∫ y, g' y ∂(ρ r)| ≤ C1 := by
    simpa using norm_integral_le_of_norm_le_const (μ := ρ r) (f := g') (ae_of_all _ hb1)
  have hb2' : |∫ y, g'' y ∂(ρ r)| ≤ C2 := by
    simpa using norm_integral_le_of_norm_le_const (μ := ρ r) (f := g'') (ae_of_all _ hb2)
  calc |b * ∫ y, g' y ∂(ρ r) + v / 2 * ∫ y, g'' y ∂(ρ r)|
      ≤ |b * ∫ y, g' y ∂(ρ r)| + |v / 2 * ∫ y, g'' y ∂(ρ r)| := abs_add_le _ _
    _ = |b| * |∫ y, g' y ∂(ρ r)| + |v / 2| * |∫ y, g'' y ∂(ρ r)| := by rw [abs_mul, abs_mul]
    _ ≤ |b| * C1 + |v| / 2 * C2 := by
        rw [show |v / 2| = |v| / 2 by rw [abs_div, abs_two]]
        exact add_le_add (mul_le_mul_of_nonneg_left hb1' (abs_nonneg b))
          (mul_le_mul_of_nonneg_left hb2' (by positivity))

/-- Two flows' pairing differences against the same admissible test are Lipschitz, with
twice the single-flow constant: the shared triangle-inequality step behind both `hUlip` and
`hWlip` in `pairing_cos_sin_eq`. -/
private lemma diff_pairing_lipschitz {b v T : ℝ} {ρ η : ℝ → Measure ℝ}
    (hρ : IsWeakForwardFlow (fun _ _ ↦ b) (fun _ _ ↦ v) T ρ)
    (hη : IsWeakForwardFlow (fun _ _ ↦ b) (fun _ _ ↦ v) T η)
    {g g' g'' g''' : ℝ → ℝ} {C1 C2 C3 : ℝ}
    (h1 : ∀ x, HasDerivAt g (g' x) x) (h2 : ∀ x, HasDerivAt g' (g'' x) x)
    (h3 : ∀ x, HasDerivAt g'' (g''' x) x)
    (hb1 : ∀ x, |g' x| ≤ C1) (hb2 : ∀ x, |g'' x| ≤ C2)
    (hb3 : ∀ x, |g''' x| ≤ C3)
    {s₀ s : ℝ} (hs₀ : s₀ ∈ Set.Icc (0 : ℝ) T) (hs : s ∈ Set.Icc (0 : ℝ) T) :
    |((∫ y, g y ∂(ρ s)) - ∫ y, g y ∂(η s)) - ((∫ y, g y ∂(ρ s₀)) - ∫ y, g y ∂(η s₀))|
      ≤ 2 * (|b| * C1 + |v| / 2 * C2) * |s - s₀| := by
  have h1' := abs_pairing_lipschitz hρ h1 h2 h3 hb1 hb2 hb3 hs₀ hs
  have h2' := abs_pairing_lipschitz hη h1 h2 h3 hb1 hb2 hb3 hs₀ hs
  calc |((∫ y, g y ∂(ρ s)) - ∫ y, g y ∂(η s)) - ((∫ y, g y ∂(ρ s₀)) - ∫ y, g y ∂(η s₀))|
      = |((∫ y, g y ∂(ρ s)) - ∫ y, g y ∂(ρ s₀)) - ((∫ y, g y ∂(η s)) - ∫ y, g y ∂(η s₀))| := by
        congr 1; ring
    _ ≤ |(∫ y, g y ∂(ρ s)) - ∫ y, g y ∂(ρ s₀)| + |(∫ y, g y ∂(η s)) - ∫ y, g y ∂(η s₀)| :=
        abs_sub _ _
    _ ≤ (|b| * C1 + |v| / 2 * C2) * |s - s₀| + (|b| * C1 + |v| / 2 * C2) * |s - s₀| :=
        add_le_add h1' h2'
    _ = 2 * (|b| * C1 + |v| / 2 * C2) * |s - s₀| := by ring

/-- A function Lipschitz on `[0, T]` (with a known-nonnegative constant) is continuous
there: the `ε`-`δ` argument shared by every Lipschitz-from-a-pairing-identity bound in
this file. -/
lemma continuousOn_Icc_of_abs_sub_le_mul_abs_sub {f : ℝ → ℝ} {T L : ℝ}
    (hLip : ∀ s₀ s, s₀ ∈ Set.Icc (0 : ℝ) T → s ∈ Set.Icc (0 : ℝ) T →
      |f s - f s₀| ≤ L * |s - s₀|) :
    ContinuousOn f (Set.Icc 0 T) :=
  (LipschitzOnWith.of_dist_le' (K := L) fun s₀ hs₀ s hs => by
    simpa [Real.dist_eq, abs_sub_comm] using hLip s₀ s hs₀ hs).continuousOn

/-- The generator's linear combination against a frequency, bounded by the sup-norm: the
shared triangle-inequality step behind both components of `hFbound` in `pairing_cos_sin_eq`
(the `ℝ × ℝ` Grönwall bound `‖F' x‖ ≤ K * ‖F x‖`). -/
lemma abs_mul_add_mul_sq_le_mul_max (b v ξ p q : ℝ) :
    |b * ξ * p + v / 2 * ξ ^ 2 * q| ≤ (|b| * |ξ| + |v| / 2 * ξ ^ 2) * max |p| |q| := by
  have hp : |p| ≤ max |p| |q| := le_max_left _ _
  have hq : |q| ≤ max |p| |q| := le_max_right _ _
  calc |b * ξ * p + v / 2 * ξ ^ 2 * q|
      ≤ |b * ξ * p| + |v / 2 * ξ ^ 2 * q| := abs_add_le _ _
    _ = |b| * |ξ| * |p| + |v| / 2 * ξ ^ 2 * |q| := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, show |v / 2| = |v| / 2 by rw [abs_div, abs_two],
          abs_of_nonneg (sq_nonneg ξ)]
    _ ≤ |b| * |ξ| * max |p| |q| + |v| / 2 * ξ ^ 2 * max |p| |q| :=
        add_le_add (mul_le_mul_of_nonneg_left hp (by positivity))
          (mul_le_mul_of_nonneg_left hq (by positivity))
    _ = (|b| * |ξ| + |v| / 2 * ξ ^ 2) * max |p| |q| := by ring

/-! ### Trigonometric test chains

`cos(ξ·)` and `sin(ξ·)` have constant-coefficient derivative chains: the
generator `b · (·)' + v/2 · (·)''` maps each to a linear combination of the
other, with no new functions appearing — the algebraic fact that drives the
Volterra system in `pairing_cos_sin_eq`. -/

/-- The derivative of `x ↦ cos (ξ * x)` is `-ξ * sin (ξ * x)`. -/
lemma hasDerivAt_cos_const_mul (ξ x : ℝ) :
    HasDerivAt (fun x => Real.cos (ξ * x)) (-ξ * Real.sin (ξ * x)) x :=
  ((Real.hasDerivAt_cos (ξ * x)).comp x (hasDerivAt_const_mul ξ)).congr_deriv (by ring)

/-- The derivative of `x ↦ -ξ * sin (ξ * x)` is `-ξ ^ 2 * cos (ξ * x)`. -/
lemma hasDerivAt_neg_mul_sin_const_mul (ξ x : ℝ) :
    HasDerivAt (fun x => -ξ * Real.sin (ξ * x)) (-ξ ^ 2 * Real.cos (ξ * x)) x :=
  (((Real.hasDerivAt_sin (ξ * x)).comp x (hasDerivAt_const_mul ξ)).const_mul (-ξ)).congr_deriv
    (by ring)

/-- The derivative of `x ↦ -ξ ^ 2 * cos (ξ * x)` is `ξ ^ 3 * sin (ξ * x)`. -/
lemma hasDerivAt_neg_sq_mul_cos_const_mul (ξ x : ℝ) :
    HasDerivAt (fun x => -ξ ^ 2 * Real.cos (ξ * x)) (ξ ^ 3 * Real.sin (ξ * x)) x :=
  (((Real.hasDerivAt_cos (ξ * x)).comp x (hasDerivAt_const_mul ξ)).const_mul
    (-ξ ^ 2)).congr_deriv (by ring)

/-- The derivative of `x ↦ sin (ξ * x)` is `ξ * cos (ξ * x)`. -/
lemma hasDerivAt_sin_const_mul (ξ x : ℝ) :
    HasDerivAt (fun x => Real.sin (ξ * x)) (ξ * Real.cos (ξ * x)) x :=
  ((Real.hasDerivAt_sin (ξ * x)).comp x (hasDerivAt_const_mul ξ)).congr_deriv (by ring)

/-- The derivative of `x ↦ ξ * cos (ξ * x)` is `-ξ ^ 2 * sin (ξ * x)`. -/
lemma hasDerivAt_mul_cos_const_mul (ξ x : ℝ) :
    HasDerivAt (fun x => ξ * Real.cos (ξ * x)) (-ξ ^ 2 * Real.sin (ξ * x)) x :=
  (((Real.hasDerivAt_cos (ξ * x)).comp x (hasDerivAt_const_mul ξ)).const_mul ξ).congr_deriv
    (by ring)

/-- The derivative of `x ↦ -ξ ^ 2 * sin (ξ * x)` is `-ξ ^ 3 * cos (ξ * x)`. -/
lemma hasDerivAt_neg_sq_mul_sin_const_mul (ξ x : ℝ) :
    HasDerivAt (fun x => -ξ ^ 2 * Real.sin (ξ * x)) (-ξ ^ 3 * Real.cos (ξ * x)) x :=
  (((Real.hasDerivAt_sin (ξ * x)).comp x (hasDerivAt_const_mul ξ)).const_mul
    (-ξ ^ 2)).congr_deriv (by ring)

/-- The sup bounds for the `cos(ξ·)` derivative chain, bundled: `C1 = |ξ|`, `C2 = ξ²`,
`C3 = |ξ|³`. -/
lemma abs_cos_derivative_chain_le (ξ : ℝ) :
    (∀ y : ℝ, |(-ξ) * Real.sin (ξ * y)| ≤ |ξ|) ∧
    (∀ y : ℝ, |(-ξ ^ 2) * Real.cos (ξ * y)| ≤ ξ ^ 2) ∧
    (∀ y : ℝ, |ξ ^ 3 * Real.sin (ξ * y)| ≤ |ξ| ^ 3) := by
  refine ⟨fun y => ?_, fun y => ?_, fun y => ?_⟩
  · rw [abs_mul]; simpa using mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg ξ)
  · rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg ξ)]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (sq_nonneg ξ)).trans_eq (mul_one _)
  · rw [abs_mul, abs_pow]
    exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity)).trans_eq (mul_one _)

/-- The sup bounds for the `sin(ξ·)` derivative chain, bundled: same constants as
`abs_cos_derivative_chain_le`. -/
lemma abs_sin_derivative_chain_le (ξ : ℝ) :
    (∀ y : ℝ, |ξ * Real.cos (ξ * y)| ≤ |ξ|) ∧
    (∀ y : ℝ, |(-ξ ^ 2) * Real.sin (ξ * y)| ≤ ξ ^ 2) ∧
    (∀ y : ℝ, |(-ξ ^ 3) * Real.cos (ξ * y)| ≤ |ξ| ^ 3) := by
  refine ⟨fun y => ?_, fun y => ?_, fun y => ?_⟩
  · rw [abs_mul]; simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg ξ)
  · rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg ξ)]
    exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (sq_nonneg ξ)).trans_eq (mul_one _)
  · rw [abs_mul, abs_neg, abs_pow]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)).trans_eq (mul_one _)

/-! ### Localizing the fundamental theorem of calculus to `[0, T]`

The pairing identity is only known on `[0, T]`; to differentiate a Volterra
primitive from the right at a point `x ∈ [0, T)` it suffices that the
integrand be continuous *near `x` within `[0, T]`* — `HasDerivWithinAt` only
sees the germ of the function within the target set, so continuity on `[0,
T]` already supplies everything `integral_hasDerivWithinAt_right` needs at
the one-sided filters `Ici x` / `Ioi x`. -/

/-- The primitive `u ↦ ∫ r in 0..u, h r` of a function continuous on `[0, T]` has right derivative
`h x` at each `x ∈ [0, T)`. -/
lemma hasDerivWithinAt_Ici_of_continuousOn {h : ℝ → ℝ} {x T : ℝ}
    (hcont : ContinuousOn h (Set.Icc 0 T)) (hx0 : 0 ≤ x) (hxT : x < T) :
    HasDerivWithinAt (fun u => ∫ r in (0 : ℝ)..u, h r) (h x) (Set.Ici x) x := by
  have hmemx : x ∈ Set.Icc (0 : ℝ) T := ⟨hx0, hxT.le⟩
  have hmem : Set.Icc (0 : ℝ) T ∈ nhdsWithin x (Set.Ioi x) :=
    Icc_mem_nhdsGT_of_mem ⟨hx0, hxT⟩
  have hmeas : StronglyMeasurableAtFilter h (nhdsWithin x (Set.Ioi x)) :=
    ⟨Set.Icc 0 T, hmem, hcont.aestronglyMeasurable measurableSet_Icc⟩
  have hb : ContinuousWithinAt h (Set.Ioi x) x := by
    have h1 : ContinuousWithinAt h (Set.Icc 0 T) x := hcont x hmemx
    have h2 : ContinuousWithinAt h (Set.Ioi x ∩ Set.Icc 0 T) x :=
      h1.mono Set.inter_subset_right
    exact (continuousWithinAt_inter' hmem).mp h2
  have hintg : IntervalIntegrable h volume 0 x :=
    ContinuousOn.intervalIntegrable_of_Icc hx0 (hcont.mono (Set.Icc_subset_Icc_right hxT.le))
  exact intervalIntegral.integral_hasDerivWithinAt_right hintg hmeas hb

/-- A function equal to its own Volterra primitive on `[0, T]` is right-differentiable there,
with derivative the (continuous) generator value: combines
`hasDerivWithinAt_Ici_of_continuousOn` (the primitive's own derivative) with the
`=ᶠ[𝓝[Ici x] x]` transfer from the primitive identity — the shared step behind both
`hCderiv` and `hSderiv` in `hasDerivWithinAt_cosPairing_sinPairing`. -/
lemma hasDerivWithinAt_of_volterra_primitive {g h : ℝ → ℝ} {x T : ℝ}
    (hcont : ContinuousOn h (Set.Icc 0 T)) (hx0 : 0 ≤ x) (hxT : x < T)
    (hprim : ∀ s ∈ Set.Icc (0 : ℝ) T, g s = g 0 + ∫ r in (0 : ℝ)..s, h r) :
    HasDerivWithinAt g (h x) (Set.Ici x) x := by
  have hderiv0 : HasDerivWithinAt (fun u => ∫ r in (0 : ℝ)..u, h r) (h x) (Set.Ici x) x :=
    hasDerivWithinAt_Ici_of_continuousOn hcont hx0 hxT
  have heq : g =ᶠ[nhdsWithin x (Set.Ici x)] (fun s => g 0 + ∫ r in (0 : ℝ)..s, h r) :=
    Filter.eventually_of_mem (Icc_mem_nhdsGE_of_mem ⟨hx0, hxT⟩) hprim
  exact (hderiv0.const_add (g 0)).congr_of_eventuallyEq_of_mem heq (le_refl x)

/-- An admissible pairing is the Volterra primitive of its generator value, once the
generator is recognized as a named function `h`: the shared `pairing_increment` + generator
rewrite step behind both `hCprim` and `hSprim` in `hasDerivWithinAt_cosPairing_sinPairing`. -/
private lemma pairing_volterra_primitive {b v T : ℝ} {μ : ℝ → Measure ℝ}
    (hμ : IsWeakForwardFlow (fun _ _ ↦ b) (fun _ _ ↦ v) T μ) (hT : 0 < T)
    {g g' g'' g''' : ℝ → ℝ} {C1 C2 C3 : ℝ}
    (h1 : ∀ x, HasDerivAt g (g' x) x) (h2 : ∀ x, HasDerivAt g' (g'' x) x)
    (h3 : ∀ x, HasDerivAt g'' (g''' x) x)
    (hb1 : ∀ x, |g' x| ≤ C1) (hb2 : ∀ x, |g'' x| ≤ C2)
    (hb3 : ∀ x, |g''' x| ≤ C3) (h : ℝ → ℝ)
    (hheq : ∀ r, h r = b * ∫ y, g' y ∂(μ r) + v / 2 * ∫ y, g'' y ∂(μ r)) :
    ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ y, g y ∂(μ s)) = (∫ y, g y ∂(μ 0)) + ∫ r in (0 : ℝ)..s, h r := by
  intro s hs
  have hinc := pairing_increment hμ h1 h2 h3 hb1 hb2 hb3 (Set.left_mem_Icc.mpr hT.le) hs
  have hcongr : (∫ r in (0 : ℝ)..s,
      (b * ∫ y, g' y ∂(μ r) + v / 2 * ∫ y, g'' y ∂(μ r))) = ∫ r in (0 : ℝ)..s, h r :=
    intervalIntegral.integral_congr fun r _ => (hheq r).symm
  rw [hcongr] at hinc
  linarith [hinc]

/-! ### The Volterra system at a fixed frequency -/

/-- For a flow obeying the weak forward equation with constant coefficients,
the pairings against `cos(ξ·)` and `sin(ξ·)` are right-differentiable on `[0,
T)`, with derivatives given by the generator applied to the paired
trigonometric test. -/
private lemma hasDerivWithinAt_cosPairing_sinPairing {b v T : ℝ} {μ : ℝ → Measure ℝ}
    (hμ : IsWeakForwardFlow (fun _ _ ↦ b) (fun _ _ ↦ v) T μ) (ξ x : ℝ) (hx0 : 0 ≤ x)
    (hxT : x < T) :
    HasDerivWithinAt (fun s => ∫ y, Real.cos (ξ * y) ∂(μ s))
      (-b * ξ * (∫ y, Real.sin (ξ * y) ∂(μ x)) - v / 2 * ξ ^ 2 * (∫ y, Real.cos (ξ * y) ∂(μ x)))
      (Set.Ici x) x ∧
    HasDerivWithinAt (fun s => ∫ y, Real.sin (ξ * y) ∂(μ s))
      (b * ξ * (∫ y, Real.cos (ξ * y) ∂(μ x)) - v / 2 * ξ ^ 2 * (∫ y, Real.sin (ξ * y) ∂(μ x)))
      (Set.Ici x) x := by
  have hT : 0 < T := hx0.trans_lt hxT
  obtain ⟨hb1, hb2, hb3⟩ := abs_cos_derivative_chain_le ξ
  obtain ⟨hb1', hb2', hb3'⟩ := abs_sin_derivative_chain_le ξ
  have hCcont : ContinuousOn (fun s => ∫ y, Real.cos (ξ * y) ∂(μ s)) (Set.Icc 0 T) :=
    continuousOn_Icc_of_abs_sub_le_mul_abs_sub fun s₀ s hs₀ hs =>
      abs_pairing_lipschitz hμ (hasDerivAt_cos_const_mul ξ) (hasDerivAt_neg_mul_sin_const_mul ξ)
        (hasDerivAt_neg_sq_mul_cos_const_mul ξ) hb1 hb2 hb3 hs₀ hs
  have hScont : ContinuousOn (fun s => ∫ y, Real.sin (ξ * y) ∂(μ s)) (Set.Icc 0 T) :=
    continuousOn_Icc_of_abs_sub_le_mul_abs_sub fun s₀ s hs₀ hs =>
      abs_pairing_lipschitz hμ (hasDerivAt_sin_const_mul ξ) (hasDerivAt_mul_cos_const_mul ξ)
        (hasDerivAt_neg_sq_mul_sin_const_mul ξ) hb1' hb2' hb3' hs₀ hs
  set h : ℝ → ℝ := fun r => -b * ξ * (∫ y, Real.sin (ξ * y) ∂(μ r))
      - v / 2 * ξ ^ 2 * (∫ y, Real.cos (ξ * y) ∂(μ r)) with hhdef
  set k : ℝ → ℝ := fun r => b * ξ * (∫ y, Real.cos (ξ * y) ∂(μ r))
      - v / 2 * ξ ^ 2 * (∫ y, Real.sin (ξ * y) ∂(μ r)) with hkdef
  have hhcont : ContinuousOn h (Set.Icc 0 T) := by
    rw [hhdef]; exact (continuousOn_const.mul hScont).sub (continuousOn_const.mul hCcont)
  have hkcont : ContinuousOn k (Set.Icc 0 T) := by
    rw [hkdef]; exact (continuousOn_const.mul hCcont).sub (continuousOn_const.mul hScont)
  have hCprim : ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ y, Real.cos (ξ * y) ∂(μ s)) = (∫ y, Real.cos (ξ * y) ∂(μ 0)) + ∫ r in (0 : ℝ)..s, h r :=
    pairing_volterra_primitive hμ hT (hasDerivAt_cos_const_mul ξ)
      (hasDerivAt_neg_mul_sin_const_mul ξ)
      (hasDerivAt_neg_sq_mul_cos_const_mul ξ) hb1 hb2 hb3 h fun r => by
        simp only [hhdef, integral_const_mul]; ring
  have hSprim : ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ y, Real.sin (ξ * y) ∂(μ s)) = (∫ y, Real.sin (ξ * y) ∂(μ 0)) + ∫ r in (0 : ℝ)..s, k r :=
    pairing_volterra_primitive hμ hT (hasDerivAt_sin_const_mul ξ) (hasDerivAt_mul_cos_const_mul ξ)
      (hasDerivAt_neg_sq_mul_sin_const_mul ξ) hb1' hb2' hb3' k fun r => by
        simp only [hkdef, integral_const_mul]; ring
  have hCderiv : HasDerivWithinAt (fun s => ∫ y, Real.cos (ξ * y) ∂(μ s)) (h x) (Set.Ici x) x :=
    hasDerivWithinAt_of_volterra_primitive hhcont hx0 hxT hCprim
  have hSderiv : HasDerivWithinAt (fun s => ∫ y, Real.sin (ξ * y) ∂(μ s)) (k x) (Set.Ici x) x :=
    hasDerivWithinAt_of_volterra_primitive hkcont hx0 hxT hSprim
  exact ⟨hCderiv, hSderiv⟩

/-- For a fixed frequency `ξ`, the pairings of `ρ` and `η` against `cos(ξ·)`
and `sin(ξ·)` agree throughout `[0, T]`, given agreement at `0`. The pairing
differences solve a linear Volterra system; a Lipschitz bound gives their
continuity, the one-sided FTC gives their right derivatives, and Grönwall's
inequality (applied to the `ℝ × ℝ`-valued pair, whose sup-norm bounds the
derivative by `K` times itself) forces both to vanish. -/
private lemma pairing_cos_sin_eq {b v T : ℝ} {ρ η : ℝ → Measure ℝ}
    (hρ : IsWeakForwardFlow (fun _ _ ↦ b) (fun _ _ ↦ v) T ρ)
    (hη : IsWeakForwardFlow (fun _ _ ↦ b) (fun _ _ ↦ v) T η)
    (hstart : ρ 0 = η 0) (ξ : ℝ) :
    ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ y, Real.cos (ξ * y) ∂(ρ s) = ∫ y, Real.cos (ξ * y) ∂(η s)) ∧
      (∫ y, Real.sin (ξ * y) ∂(ρ s) = ∫ y, Real.sin (ξ * y) ∂(η s)) := by
  obtain ⟨hb1, hb2, hb3⟩ := abs_cos_derivative_chain_le ξ
  obtain ⟨hb1', hb2', hb3'⟩ := abs_sin_derivative_chain_le ξ
  set K : ℝ := |b| * |ξ| + |v| / 2 * ξ ^ 2 with hKdef
  set U : ℝ → ℝ := fun s => (∫ y, Real.cos (ξ * y) ∂(ρ s)) - ∫ y, Real.cos (ξ * y) ∂(η s)
    with hUdef
  set W : ℝ → ℝ := fun s => (∫ y, Real.sin (ξ * y) ∂(ρ s)) - ∫ y, Real.sin (ξ * y) ∂(η s)
    with hWdef
  have hUlip : ∀ s₀ s, s₀ ∈ Set.Icc (0 : ℝ) T → s ∈ Set.Icc (0 : ℝ) T →
      |U s - U s₀| ≤ 2 * K * |s - s₀| := by
    intro s₀ s hs₀ hs
    have := diff_pairing_lipschitz hρ hη (hasDerivAt_cos_const_mul ξ)
      (hasDerivAt_neg_mul_sin_const_mul ξ)
      (hasDerivAt_neg_sq_mul_cos_const_mul ξ) hb1 hb2 hb3 hs₀ hs
    simpa only [hUdef, hKdef] using this
  have hWlip : ∀ s₀ s, s₀ ∈ Set.Icc (0 : ℝ) T → s ∈ Set.Icc (0 : ℝ) T →
      |W s - W s₀| ≤ 2 * K * |s - s₀| := by
    intro s₀ s hs₀ hs
    have := diff_pairing_lipschitz hρ hη (hasDerivAt_sin_const_mul ξ)
      (hasDerivAt_mul_cos_const_mul ξ)
      (hasDerivAt_neg_sq_mul_sin_const_mul ξ) hb1' hb2' hb3' hs₀ hs
    simpa only [hWdef, hKdef] using this
  have hUcont : ContinuousOn U (Set.Icc 0 T) := continuousOn_Icc_of_abs_sub_le_mul_abs_sub hUlip
  have hWcont : ContinuousOn W (Set.Icc 0 T) := continuousOn_Icc_of_abs_sub_le_mul_abs_sub hWlip
  set F : ℝ → ℝ × ℝ := fun s => (U s, W s) with hFdef
  set F' : ℝ → ℝ × ℝ := fun x => (-b * ξ * W x - v / 2 * ξ ^ 2 * U x,
      b * ξ * U x - v / 2 * ξ ^ 2 * W x) with hF'def
  have hFcont : ContinuousOn F (Set.Icc 0 T) := hUcont.prodMk hWcont
  have hFderiv : ∀ x ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt F (F' x) (Set.Ici x) x := by
    intro x hx
    obtain ⟨hx0, hxT⟩ := hx
    obtain ⟨hCρ, hSρ⟩ := hasDerivWithinAt_cosPairing_sinPairing hρ ξ x hx0 hxT
    obtain ⟨hCη, hSη⟩ := hasDerivWithinAt_cosPairing_sinPairing hη ξ x hx0 hxT
    have hU' : HasDerivWithinAt U (-b * ξ * W x - v / 2 * ξ ^ 2 * U x) (Set.Ici x) x := by
      refine (hCρ.sub hCη).congr_deriv ?_
      simp only [hUdef, hWdef]
      ring
    have hW' : HasDerivWithinAt W (b * ξ * U x - v / 2 * ξ ^ 2 * W x) (Set.Ici x) x := by
      refine (hSρ.sub hSη).congr_deriv ?_
      simp only [hUdef, hWdef]
      ring
    exact hU'.prodMk hW'
  have hF0 : F 0 = 0 := by
    have hU0 : U 0 = 0 := by simp only [hUdef, hstart, sub_self]
    have hW0 : W 0 = 0 := by simp only [hWdef, hstart, sub_self]
    simp [hFdef, hU0, hW0]
  have hFbound : ∀ x ∈ Set.Ico (0 : ℝ) T, ‖F' x‖ ≤ K * ‖F x‖ := by
    intro x _
    rw [hF'def, hFdef, Prod.norm_mk, Prod.norm_mk]
    apply max_le
    · have heq : (-b * ξ * W x - v / 2 * ξ ^ 2 * U x)
          = b * ξ * (-W x) + v / 2 * ξ ^ 2 * (-U x) := by ring
      rw [heq]
      have hb := abs_mul_add_mul_sq_le_mul_max b v ξ (-W x) (-U x)
      rwa [abs_neg, abs_neg, max_comm, ← hKdef] at hb
    · have heq : (b * ξ * U x - v / 2 * ξ ^ 2 * W x) = b * ξ * U x + v / 2 * ξ ^ 2 * (-W x) := by
        ring
      rw [heq]
      have hb := abs_mul_add_mul_sq_le_mul_max b v ξ (U x) (-W x)
      rwa [abs_neg, ← hKdef] at hb
  have hFzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hFcont hFderiv hF0 hFbound
  intro s hs
  have hz := hFzero s hs
  rw [hFdef] at hz
  have hUz : U s = 0 := by have := congrArg Prod.fst hz; simpa using this
  have hWz : W s = 0 := by have := congrArg Prod.snd hz; simpa using this
  refine ⟨?_, ?_⟩
  · have := hUz; rw [hUdef] at this; linarith [this]
  · have := hWz; rw [hWdef] at this; linarith [this]

/-- The characteristic function of a probability measure, split into its real/imaginary
`cos`/`sin` pairings: the shared computation behind both sides of `weakForwardUniqueConst`'s
`charFun` comparison (applied once to `ρ s`, once to `η s`). -/
lemma charFun_eq_cos_add_sin_mul_I {μ : Measure ℝ} [IsProbabilityMeasure μ] (ξ : ℝ) :
    charFun μ ξ = ((∫ x, Real.cos (ξ * x) ∂μ : ℝ) : ℂ)
      + ((∫ x, Real.sin (ξ * x) ∂μ : ℝ) : ℂ) * Complex.I := by
  have hexp : ∀ x : ℝ, Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)
      = (Real.cos (ξ * x) : ℂ) + (Real.sin (ξ * x) : ℂ) * Complex.I := by
    intro x
    rw [show ((ξ : ℂ) * (x : ℂ)) = ((ξ * x : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have hint : ∀ g : ℝ → ℝ, Continuous g → (∀ x, |g x| ≤ 1) →
      Integrable (fun x => (g x : ℂ)) μ := fun g hgc hg =>
    Integrable.mono' (integrable_const (1 : ℝ))
      (Complex.continuous_ofReal.comp hgc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simp only [Complex.norm_real, Real.norm_eq_abs]; exact hg x)
  rw [charFun_apply_real]
  simp_rw [hexp]
  rw [integral_add (hint _ (by fun_prop) fun x => Real.abs_cos_le_one (ξ * x))
    ((hint _ (by fun_prop) fun x => Real.abs_sin_le_one (ξ * x)).mul_const Complex.I),
    integral_mul_const, integral_complex_ofReal, integral_complex_ofReal]

/-- **Weak uniqueness for the constant-coefficient forward equation.** Two flows solving
`IsWeakForwardFlow` with the same constant coefficients (`afn ≡ b`, `bfn ≡ v`) and the same
initial law coincide at every time in `(0, T]`. -/
theorem weakForwardUniqueConst {ρ η : ℝ → Measure ℝ} {b v T : ℝ}
    (hρ : IsWeakForwardFlow (fun _ _ ↦ b) (fun _ _ ↦ v) T ρ)
    (hη : IsWeakForwardFlow (fun _ _ ↦ b) (fun _ _ ↦ v) T η)
    (hstart : ρ 0 = η 0) :
    ∀ s ∈ Set.Ioc (0 : ℝ) T, ρ s = η s := by
  intro s hs
  have := hρ.1 s
  have := hη.1 s
  have hsIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2⟩
  refine Measure.ext_of_charFun (funext fun ξ => ?_)
  obtain ⟨hc, hsi⟩ := pairing_cos_sin_eq hρ hη hstart ξ s hsIcc
  rw [charFun_eq_cos_add_sin_mul_I, charFun_eq_cos_add_sin_mul_I, hc, hsi]

end MathFin
