/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Français 9115: the vibrating lamina, Euler's memoir of 1779 and the « Remarques »

Adapted from `lean/Germain/Fr9115Elasticity.lean` of
https://github.com/Commutator-IO/germain-project
at commit `167c171` (CC0, same author).

The modernised reading `transcripts/fr-9115/fr-9115.modern.tex` gives, from views 144–206, a
Latin copy of Euler's *Investigatio motuum quibus laminae et virgae elasticae contremiscunt*
(Acta Petropolitana 1779), then, from views 208–396, a critique of its §§ 47–51 in Sophie
Germain's working hand (« Remarques sur le mémoire d'Euler »), and, from views 398–415, the
opening of the memoir for the Institut on vibrating plates. This file proves the mathematical
statements of those sections that can be stated in mathlib.

* **The general solution (§ 9, views 153–156).** `modeY ω a b c d u = a cosh ωu + b sinh ωu +
  c cos ωu + d sin ωu`, equal to Euler's `α e^{ωu} + β e^{-ωu} + γ sin ωu + δ cos ωu`
  (`eulerY_eq_modeY`), solves `Y'''' = ω⁴ Y` (`modeY_ode`, `eulerY_ode`), and the regular
  vibration `y = C sin(ζ + √(2g/k) t) Y(s/f)` solves Euler's `∂ₜ² y = -2g b c² ∂ₛ⁴ y` when
  `f⁴ = b c² k` (`regular_vibration`). The time factor is `√(2g/k)`, as the reading corrects.
* **The six cases (§ 14).** For each pair of end conditions (free `Y'' = Y''' = 0`, supported
  `Y = Y'' = 0`, clamped `Y = Y' = 0`), a nonzero mode exists iff the 4 × 4 determinant
  vanishes (`exists_mode_iff`), and the determinant is computed: `cos ω cosh ω = 1` (I and VI),
  `sin ω cosh ω = cos ω sinh ω` (II and V), `cos ω cosh ω = -1` (III), `sin ω = 0` (IV).
* **The roots (§§ 16–17, 30).** `cos x cosh x < 1` on `]0, 3π/2]`; the first positive root of
  `cos ω cosh ω = 1` is the only root in `]0, 2π[` and lies in `]3π/2, 3π/2 + 1/50[`
  (`first_root_free_free`); `cos ω cosh ω = -1` has a root in `]π/2, π[`.
* **§ 47, three supports.** Euler's final equation equals
  `-4e^ω (sinh ω sin λω sin μω − sin ω sinh λω sinh μω)/(sin λω sin μω)` (`eulerFinal_eq`), the
  form of the « Remarques » § 2 is Euler's times `sin λω sin μω` (`germainForm_eq`), its
  division by `e^{2λω} − 1` for `λ = 1/n` holds (`germain_geom_form`), and the equation is the
  `coth/cot` equation (`final_iff_coth`); for `λ = ½` it factors (`half_factor`,
  `euler_half_bracket`).
* **The critique.** Germain's computation of § 1 holds (`objection_sin_eq_tanh`,
  `objection_sin_zero`), but its conclusion does not: the second family is a genuine mode of
  the supported lamina held at its middle, with a nonzero jump of `y'''` at the stylet
  (`second_family_is_mode`). Euler's printed `γ' = -γ` (§ 50) breaks the slope at the stylet,
  `γ' = γ` satisfies the eight conditions (`first_family_sign`). Modes without force sit at
  rational positions only (`sympathetic_iff_rational`); the arithmetic of the § 5 series
  (`common_term_iff`).
* **The free lamina touched by a stylet (§ 8, view 342).** For positive frequency and an interior
  stylet position, a nonzero mode in this family satisfying the eight conditions exists iff
  `C₊(μω) P(λω) + C₊(λω) P(μω) = 0`, `P t = cosh t sin t − sinh t
  cos t`, `C₊ t = 1 + cosh t cos t` (`free_stylet_iff`); at `λ = ½` the family `C₊(ω/2) = 0`,
  which § 9 rejects, is a genuine mode (`free_stylet_half`), though not a mode of the free
  lamina (`cplus_incompatible`).
* **The plate (memoir for the Institut, §§ 1–2, views 403–406).** The factorisation of (B)
  and the splitting of its solutions (`factor_B_left`, `factor_B_split`), the integral (C)
  (`plate_C`), the integral (D) with its sound and its supported square edges (`plate_D`,
  `plate_D_boundary`, `plate_D_sound`).

Not formalised: that the four functions span all solutions of the fourth-order ODE (the
statements are about this family, which is Euler's), the 8 × 8 determinant itself (the stylet
theorem is proved by elimination), the numerical roots beyond the bounds above, the clamped
form of § 12, the series (E)–(I) and the square plate of § 4, the heat leaves.
-/

@[expose] public section

namespace LeanPool.SophieGermainArchives.Fr9115Elasticity

open Real

/-! ## The general solution of `Y'''' = ω⁴ Y` -/

/-- `Y(u) = a cosh ωu + b sinh ωu + c cos ωu + d sin ωu`. -/
noncomputable def modeY (ω a b c d : ℝ) : ℝ → ℝ :=
  fun u => a * cosh (ω * u) + b * sinh (ω * u) + c * cos (ω * u) + d * sin (ω * u)

/-- Euler's form (§ 9): `α e^{ωu} + β e^{-ωu} + γ sin ωu + δ cos ωu`. -/
noncomputable def eulerY (ω α β γ δ : ℝ) : ℝ → ℝ :=
  fun u => α * exp (ω * u) + β * exp (-(ω * u)) + γ * sin (ω * u) + δ * cos (ω * u)

theorem eulerY_eq_modeY (ω α β γ δ : ℝ) :
    eulerY ω α β γ δ = modeY ω (α + β) (α - β) δ γ := by
  funext u
  simp only [eulerY, modeY, cosh_eq, sinh_eq]
  ring

theorem modeY_apply (ω a b c d u : ℝ) :
    modeY ω a b c d u =
      a * cosh (ω * u) + b * sinh (ω * u) + c * cos (ω * u) + d * sin (ω * u) := rfl

theorem modeY_ext {ω a b c d a' b' c' d' : ℝ} (h₁ : a = a') (h₂ : b = b') (h₃ : c = c')
    (h₄ : d = d') : modeY ω a b c d = modeY ω a' b' c' d' := by
  subst h₁ h₂ h₃ h₄; rfl

theorem hasDerivAt_modeY (ω a b c d u : ℝ) :
    HasDerivAt (modeY ω a b c d) (modeY ω (ω * b) (ω * a) (ω * d) (-(ω * c)) u) u := by
  have h : HasDerivAt (fun x : ℝ => ω * x) ω u := by
    simpa using (hasDerivAt_id' u).const_mul ω
  have := (((h.cosh.const_mul a).add (h.sinh.const_mul b)).add (h.cos.const_mul c)).add
    (h.sin.const_mul d)
  exact this.congr_deriv (by simp only [modeY]; ring)

theorem deriv_modeY (ω a b c d : ℝ) :
    deriv (modeY ω a b c d) = modeY ω (ω * b) (ω * a) (ω * d) (-(ω * c)) :=
  funext fun u => (hasDerivAt_modeY ω a b c d u).deriv

theorem iteratedDeriv_one_modeY (ω a b c d : ℝ) :
    iteratedDeriv 1 (modeY ω a b c d) = modeY ω (ω * b) (ω * a) (ω * d) (-(ω * c)) := by
  rw [iteratedDeriv_one, deriv_modeY]

theorem iteratedDeriv_two_modeY (ω a b c d : ℝ) :
    iteratedDeriv 2 (modeY ω a b c d) =
      modeY ω (ω ^ 2 * a) (ω ^ 2 * b) (-(ω ^ 2 * c)) (-(ω ^ 2 * d)) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one_modeY, deriv_modeY]
  exact modeY_ext (by ring) (by ring) (by ring) (by ring)

theorem iteratedDeriv_three_modeY (ω a b c d : ℝ) :
    iteratedDeriv 3 (modeY ω a b c d) =
      modeY ω (ω ^ 3 * b) (ω ^ 3 * a) (-(ω ^ 3 * d)) (ω ^ 3 * c) := by
  rw [iteratedDeriv_succ, iteratedDeriv_two_modeY, deriv_modeY]
  exact modeY_ext (by ring) (by ring) (by ring) (by ring)

theorem iteratedDeriv_four_modeY (ω a b c d : ℝ) :
    iteratedDeriv 4 (modeY ω a b c d) =
      modeY ω (ω ^ 4 * a) (ω ^ 4 * b) (ω ^ 4 * c) (ω ^ 4 * d) := by
  rw [iteratedDeriv_succ, iteratedDeriv_three_modeY, deriv_modeY]
  exact modeY_ext (by ring) (by ring) (by ring) (by ring)

/-- The fourth-order equation of § 5 in reduced form: `Y'''' = ω⁴ Y`. -/
theorem modeY_ode (ω a b c d u : ℝ) :
    iteratedDeriv 4 (modeY ω a b c d) u = ω ^ 4 * modeY ω a b c d u := by
  rw [iteratedDeriv_four_modeY]; simp only [modeY]; ring

/-- Euler's own form solves the same equation. -/
theorem eulerY_ode (ω α β γ δ u : ℝ) :
    iteratedDeriv 4 (eulerY ω α β γ δ) u = ω ^ 4 * eulerY ω α β γ δ u := by
  rw [eulerY_eq_modeY]; exact modeY_ode _ _ _ _ _ _

theorem deriv_modeY_apply (ω a b c d u : ℝ) :
    deriv (modeY ω a b c d) u =
      ω * (b * cosh (ω * u) + a * sinh (ω * u) + d * cos (ω * u) - c * sin (ω * u)) := by
  rw [deriv_modeY]; simp only [modeY]; ring

theorem iteratedDeriv_two_modeY_apply (ω a b c d u : ℝ) :
    iteratedDeriv 2 (modeY ω a b c d) u =
      ω ^ 2 * (a * cosh (ω * u) + b * sinh (ω * u) - c * cos (ω * u) - d * sin (ω * u)) := by
  rw [iteratedDeriv_two_modeY]; simp only [modeY]; ring

theorem iteratedDeriv_three_modeY_apply (ω a b c d u : ℝ) :
    iteratedDeriv 3 (modeY ω a b c d) u =
      ω ^ 3 * (b * cosh (ω * u) + a * sinh (ω * u) - d * cos (ω * u) + c * sin (ω * u)) := by
  rw [iteratedDeriv_three_modeY]; simp only [modeY]; ring

private theorem deriv_zero_fun (x : ℝ) : deriv (0 : ℝ → ℝ) x = 0 :=
  deriv_const x (0 : ℝ)

/-- For `ω ≠ 0` the four functions are independent: a mode vanishes identically only when its
four coefficients do. -/
theorem modeY_eq_zero_iff {ω : ℝ} (hω : ω ≠ 0) {a b c d : ℝ} :
    modeY ω a b c d = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  constructor
  · intro h
    have e1 : modeY ω (ω * b) (ω * a) (ω * d) (-(ω * c)) = 0 := by
      rw [← deriv_modeY, h]; funext x; exact deriv_zero_fun x
    have e2 : modeY ω (ω * (ω * a)) (ω * (ω * b)) (ω * (-(ω * c))) (-(ω * (ω * d))) = 0 := by
      rw [← deriv_modeY, e1]; funext x; exact deriv_zero_fun x
    have e3 : modeY ω (ω * (ω * (ω * b))) (ω * (ω * (ω * a))) (ω * (-(ω * (ω * d))))
        (-(ω * (ω * (-(ω * c))))) = 0 := by
      rw [← deriv_modeY, e2]; funext x; exact deriv_zero_fun x
    have k0 := congrFun h 0
    have k1 := congrFun e1 0
    have k2 := congrFun e2 0
    have k3 := congrFun e3 0
    simp only [modeY, mul_zero, cosh_zero, sinh_zero, cos_zero, sin_zero, Pi.zero_apply]
      at k0 k1 k2 k3
    have hb : ω * (b + d) = 0 := by linear_combination k1
    have ha : ω ^ 2 * (a - c) = 0 := by linear_combination k2
    have hb' : ω ^ 3 * (b - d) = 0 := by linear_combination k3
    have ha' := (mul_eq_zero.mp ha).resolve_left (pow_ne_zero 2 hω)
    have hb2 := (mul_eq_zero.mp hb).resolve_left hω
    have hb3 := (mul_eq_zero.mp hb').resolve_left (pow_ne_zero 3 hω)
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    funext u; simp [modeY]

/-! ## The second portion, written from the far end -/

/-- `s · Y(1 - u)`: the expression of a portion described from the end `u = 1`. -/
noncomputable def reflY (ω a b c d s : ℝ) : ℝ → ℝ := fun u => s * modeY ω a b c d (1 - u)

theorem reflY_ext {ω a b c d s a' b' c' d' s' : ℝ} (h₁ : a = a') (h₂ : b = b') (h₃ : c = c')
    (h₄ : d = d') (h₅ : s = s') : reflY ω a b c d s = reflY ω a' b' c' d' s' := by
  subst h₁ h₂ h₃ h₄ h₅; rfl

theorem hasDerivAt_reflY (ω a b c d s u : ℝ) :
    HasDerivAt (reflY ω a b c d s) (reflY ω (ω * b) (ω * a) (ω * d) (-(ω * c)) (-s) u) u := by
  have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) u := (hasDerivAt_id' u).const_sub 1
  have h2 := ((hasDerivAt_modeY ω a b c d (1 - u)).comp u h1).const_mul s
  exact h2.congr_deriv (by simp only [reflY]; ring)

theorem deriv_reflY (ω a b c d s : ℝ) :
    deriv (reflY ω a b c d s) = reflY ω (ω * b) (ω * a) (ω * d) (-(ω * c)) (-s) :=
  funext fun u => (hasDerivAt_reflY ω a b c d s u).deriv

theorem iteratedDeriv_two_reflY (ω a b c d s : ℝ) :
    iteratedDeriv 2 (reflY ω a b c d s) =
      reflY ω (ω ^ 2 * a) (ω ^ 2 * b) (-(ω ^ 2 * c)) (-(ω ^ 2 * d)) s := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_reflY, deriv_reflY]
  exact reflY_ext (by ring) (by ring) (by ring) (by ring) (by ring)

theorem iteratedDeriv_three_reflY (ω a b c d s : ℝ) :
    iteratedDeriv 3 (reflY ω a b c d s) =
      reflY ω (ω ^ 3 * b) (ω ^ 3 * a) (-(ω ^ 3 * d)) (ω ^ 3 * c) (-s) := by
  rw [iteratedDeriv_succ, iteratedDeriv_two_reflY, deriv_reflY]
  exact reflY_ext (by ring) (by ring) (by ring) (by ring) (by ring)

theorem reflY_apply (ω a b c d s u : ℝ) :
    reflY ω a b c d s u = s * (a * cosh (ω * (1 - u)) + b * sinh (ω * (1 - u)) +
      c * cos (ω * (1 - u)) + d * sin (ω * (1 - u))) := rfl

theorem deriv_reflY_apply (ω a b c d s u : ℝ) :
    deriv (reflY ω a b c d s) u = -s * (ω * (b * cosh (ω * (1 - u)) + a * sinh (ω * (1 - u)) +
      d * cos (ω * (1 - u)) - c * sin (ω * (1 - u)))) := by
  rw [deriv_reflY]; simp only [reflY, modeY]; ring

theorem iteratedDeriv_two_reflY_apply (ω a b c d s u : ℝ) :
    iteratedDeriv 2 (reflY ω a b c d s) u = s * (ω ^ 2 * (a * cosh (ω * (1 - u)) +
      b * sinh (ω * (1 - u)) - c * cos (ω * (1 - u)) - d * sin (ω * (1 - u)))) := by
  rw [iteratedDeriv_two_reflY]; simp only [reflY, modeY]; ring

theorem iteratedDeriv_three_reflY_apply (ω a b c d s u : ℝ) :
    iteratedDeriv 3 (reflY ω a b c d s) u = -s * (ω ^ 3 * (b * cosh (ω * (1 - u)) +
      a * sinh (ω * (1 - u)) - d * cos (ω * (1 - u)) + c * sin (ω * (1 - u)))) := by
  rw [iteratedDeriv_three_reflY]; simp only [reflY, modeY]; ring

/-- The reflected portion vanishes identically iff the underlying mode does. -/
theorem reflY_one_eq_zero_iff (ω a b c d : ℝ) :
    reflY ω a b c d 1 = 0 ↔ modeY ω a b c d = 0 := by
  constructor
  · intro h; funext x
    have := congrFun h (1 - x)
    simpa [reflY] using this
  · intro h; funext x; simp [reflY, h]

/-! ## The regular vibrations (§ 9) -/

/-- Euler's regular vibration `y = C sin(ζ + √(2g/k) t) · Y(s/f)` solves
`∂ₜ² y = -2g b c² ∂ₛ⁴ y` as soon as `f⁴ = b c² k`. -/
theorem regular_vibration (g b c k f C ζ α β γ δ t s : ℝ) (hk : 0 < k) (hg : 0 ≤ g)
    (hf : f ≠ 0) (hf4 : f ^ 4 = b * c ^ 2 * k) :
    iteratedDeriv 2 (fun t => C * sin (ζ + √(2 * g / k) * t) * eulerY (1 / f) α β γ δ s) t =
      -(2 * g * b * c ^ 2) *
        iteratedDeriv 4 (fun s => C * sin (ζ + √(2 * g / k) * t) * eulerY (1 / f) α β γ δ s) s := by
  have hν2 : √(2 * g / k) ^ 2 = 2 * g / k := sq_sqrt (div_nonneg (by linarith) hk.le)
  have hbc : b * c ^ 2 * k ≠ 0 := by rw [← hf4]; exact pow_ne_zero 4 hf
  have hb : b ≠ 0 := by rintro rfl; apply hbc; ring
  have hc : c ≠ 0 := by rintro rfl; apply hbc; ring
  have ht : (fun t => C * sin (ζ + √(2 * g / k) * t) * eulerY (1 / f) α β γ δ s) =
      modeY (√(2 * g / k)) 0 0 (C * eulerY (1 / f) α β γ δ s * sin ζ)
        (C * eulerY (1 / f) α β γ δ s * cos ζ) := by
    funext t; simp only [modeY, sin_add]; ring
  have hs : (fun s => C * sin (ζ + √(2 * g / k) * t) * eulerY (1 / f) α β γ δ s) =
      eulerY (1 / f) (C * sin (ζ + √(2 * g / k) * t) * α) (C * sin (ζ + √(2 * g / k) * t) * β)
        (C * sin (ζ + √(2 * g / k) * t) * γ) (C * sin (ζ + √(2 * g / k) * t) * δ) := by
    funext s; simp only [eulerY]; ring
  rw [ht, hs, iteratedDeriv_two_modeY, eulerY_ode]
  simp only [modeY, eulerY]
  rw [hν2, one_div_pow, hf4, sin_add]
  field_simp
  ring

/-! ## The six cases (§§ 13–14): end conditions and frequency equations -/

/-- The row giving `Y^{(k)}(u) / ω^k` in the basis `(cosh, sinh, cos, sin)` at `x = ωu`. -/
noncomputable def rowv : ℕ → ℝ → Fin 4 → ℝ
  | 0, x => ![cosh x, sinh x, cos x, sin x]
  | 1, x => ![sinh x, cosh x, -sin x, cos x]
  | 2, x => ![cosh x, sinh x, -cos x, -sin x]
  | 3, x => ![sinh x, cosh x, sin x, -cos x]
  | _, _ => 0

/-- The mode with coefficient vector `v`. -/
noncomputable def modeV (ω : ℝ) (v : Fin 4 → ℝ) : ℝ → ℝ := modeY ω (v 0) (v 1) (v 2) (v 3)

theorem iteratedDeriv_modeV (ω : ℝ) (v : Fin 4 → ℝ) {k : ℕ} (hk : k ≤ 3) (u : ℝ) :
    iteratedDeriv k (modeV ω v) u = ω ^ k * (rowv k (ω * u) ⬝ᵥ v) := by
  interval_cases k
  · simp only [iteratedDeriv_zero, modeV]
    simp [modeY, rowv, dotProduct, Fin.sum_univ_four]
    ring
  · simp only [iteratedDeriv_one_modeY, modeV]
    simp [modeY, rowv, dotProduct, Fin.sum_univ_four]
    ring
  · simp only [iteratedDeriv_two_modeY, modeV]
    simp [modeY, rowv, dotProduct, Fin.sum_univ_four]
    ring
  · simp only [iteratedDeriv_three_modeY, modeV]
    simp [modeY, rowv, dotProduct, Fin.sum_univ_four]
    ring

/-- The three states of an end (§ 13): free, supported (« simpliciter fixus »), clamped
(« infixus »). -/
inductive EndKind
  | free
  | supported
  | clamped

/-- The two derivatives that vanish at an end of that kind: the first of them. -/
def EndKind.o₁ : EndKind → ℕ
  | .free => 2
  | .supported => 0
  | .clamped => 0

/-- The second of the two derivatives that vanish at an end of that kind. -/
def EndKind.o₂ : EndKind → ℕ
  | .free => 3
  | .supported => 2
  | .clamped => 1

theorem EndKind.o₁_le (e : EndKind) : e.o₁ ≤ 3 := by cases e <;> decide
theorem EndKind.o₂_le (e : EndKind) : e.o₂ ≤ 3 := by cases e <;> decide

/-- The end conditions at `u = 0` (kind `e₀`) and `u = 1` (kind `e₁`). -/
abbrev BC (e₀ e₁ : EndKind) (Y : ℝ → ℝ) : Prop :=
  iteratedDeriv e₀.o₁ Y 0 = 0 ∧ iteratedDeriv e₀.o₂ Y 0 = 0 ∧
    iteratedDeriv e₁.o₁ Y 1 = 0 ∧ iteratedDeriv e₁.o₂ Y 1 = 0

/-- The matrix of the four end conditions. -/
noncomputable def bcMatrix (e₀ e₁ : EndKind) (ω : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![rowv e₀.o₁ 0, rowv e₀.o₂ 0, rowv e₁.o₁ ω, rowv e₁.o₂ ω]

theorem bc_iff {ω : ℝ} (hω : ω ≠ 0) (e₀ e₁ : EndKind) (v : Fin 4 → ℝ) :
    BC e₀ e₁ (modeV ω v) ↔ (bcMatrix e₀ e₁ ω).mulVec v = 0 := by
  have hk : ∀ k : ℕ, ω ^ k ≠ 0 := fun k => pow_ne_zero k hω
  rw [BC, iteratedDeriv_modeV ω v (EndKind.o₁_le e₀), iteratedDeriv_modeV ω v (EndKind.o₂_le e₀),
    iteratedDeriv_modeV ω v (EndKind.o₁_le e₁), iteratedDeriv_modeV ω v (EndKind.o₂_le e₁)]
  simp only [mul_zero, mul_one, mul_eq_zero, hk, false_or]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    funext i
    fin_cases i
    · simpa [bcMatrix, Matrix.mulVec] using h0
    · simpa [bcMatrix, Matrix.mulVec] using h1
    · simpa [bcMatrix, Matrix.mulVec] using h2
    · simpa [bcMatrix, Matrix.mulVec] using h3
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [bcMatrix, Matrix.mulVec] using congrFun h 0
    · simpa [bcMatrix, Matrix.mulVec] using congrFun h 1
    · simpa [bcMatrix, Matrix.mulVec] using congrFun h 2
    · simpa [bcMatrix, Matrix.mulVec] using congrFun h 3

/-- A nonzero coefficient vector satisfying the four end conditions exists iff the
determinant vanishes. -/
theorem exists_mode_iff {ω : ℝ} (hω : ω ≠ 0) (e₀ e₁ : EndKind) :
    (∃ v : Fin 4 → ℝ, v ≠ 0 ∧ BC e₀ e₁ (modeV ω v)) ↔ (bcMatrix e₀ e₁ ω).det = 0 := by
  simp_rw [bc_iff hω e₀ e₁]
  exact Matrix.exists_mulVec_eq_zero_iff

theorem det_free_free (ω : ℝ) : (bcMatrix .free .free ω).det = 2 - 2 * (cos ω * cosh ω) := by
  simp only [bcMatrix, EndKind.o₁, EndKind.o₂, rowv]
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_unique, Fin.default_eq_zero]
  simp [Matrix.submatrix, Fin.succAbove, Fin.lt_def]
  linear_combination cosh_sq ω + sin_sq_add_cos_sq ω

theorem det_free_supported (ω : ℝ) :
    (bcMatrix .free .supported ω).det = 2 * (cos ω * sinh ω - cosh ω * sin ω) := by
  simp only [bcMatrix, EndKind.o₁, EndKind.o₂, rowv]
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_unique, Fin.default_eq_zero]
  simp [Matrix.submatrix, Fin.succAbove, Fin.lt_def]
  ring

theorem det_free_clamped (ω : ℝ) :
    (bcMatrix .free .clamped ω).det = 2 + 2 * (cos ω * cosh ω) := by
  simp only [bcMatrix, EndKind.o₁, EndKind.o₂, rowv]
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_unique, Fin.default_eq_zero]
  simp [Matrix.submatrix, Fin.succAbove, Fin.lt_def]
  linear_combination cosh_sq ω + sin_sq_add_cos_sq ω

theorem det_supported_supported (ω : ℝ) :
    (bcMatrix .supported .supported ω).det = -4 * (sinh ω * sin ω) := by
  simp only [bcMatrix, EndKind.o₁, EndKind.o₂, rowv]
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_unique, Fin.default_eq_zero]
  simp [Matrix.submatrix, Fin.succAbove, Fin.lt_def]
  ring

theorem det_supported_clamped (ω : ℝ) :
    (bcMatrix .supported .clamped ω).det = 2 * (sinh ω * cos ω - sin ω * cosh ω) := by
  simp only [bcMatrix, EndKind.o₁, EndKind.o₂, rowv]
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_unique, Fin.default_eq_zero]
  simp [Matrix.submatrix, Fin.succAbove, Fin.lt_def]
  ring

theorem det_clamped_clamped (ω : ℝ) :
    (bcMatrix .clamped .clamped ω).det = 2 - 2 * (cos ω * cosh ω) := by
  simp only [bcMatrix, EndKind.o₁, EndKind.o₂, rowv]
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.det_unique, Fin.default_eq_zero]
  simp [Matrix.submatrix, Fin.succAbove, Fin.lt_def]
  linear_combination cosh_sq ω + sin_sq_add_cos_sq ω

/-- Case I, both ends free: `cos ω cosh ω = 1`. -/
theorem case_I {ω : ℝ} (hω : ω ≠ 0) :
    (∃ v : Fin 4 → ℝ, v ≠ 0 ∧ BC .free .free (modeV ω v)) ↔ cos ω * cosh ω = 1 := by
  rw [exists_mode_iff hω, det_free_free]; constructor <;> intro h <;> linarith

/-- Case II, free and supported: `tan ω = tanh ω`, written `sin ω cosh ω = cos ω sinh ω`. -/
theorem case_II {ω : ℝ} (hω : ω ≠ 0) :
    (∃ v : Fin 4 → ℝ, v ≠ 0 ∧ BC .free .supported (modeV ω v)) ↔
      sin ω * cosh ω = cos ω * sinh ω := by
  rw [exists_mode_iff hω, det_free_supported]; constructor <;> intro h <;> linarith

/-- Case III, free and clamped: `cos ω cosh ω = -1`. -/
theorem case_III {ω : ℝ} (hω : ω ≠ 0) :
    (∃ v : Fin 4 → ℝ, v ≠ 0 ∧ BC .free .clamped (modeV ω v)) ↔ cos ω * cosh ω = -1 := by
  rw [exists_mode_iff hω, det_free_clamped]; constructor <;> intro h <;> linarith

/-- Case IV, both ends supported: `sin ω = 0`. -/
theorem case_IV {ω : ℝ} (hω : ω ≠ 0) :
    (∃ v : Fin 4 → ℝ, v ≠ 0 ∧ BC .supported .supported (modeV ω v)) ↔ sin ω = 0 := by
  rw [exists_mode_iff hω, det_supported_supported]
  have hs : sinh ω ≠ 0 := fun h => hω (sinh_eq_zero.mp h)
  constructor
  · intro h
    have : sinh ω * sin ω = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hs
  · intro h; rw [h]; ring

/-- Case V, supported and clamped: the equation of case II. -/
theorem case_V {ω : ℝ} (hω : ω ≠ 0) :
    (∃ v : Fin 4 → ℝ, v ≠ 0 ∧ BC .supported .clamped (modeV ω v)) ↔
      sin ω * cosh ω = cos ω * sinh ω := by
  rw [exists_mode_iff hω, det_supported_clamped]; constructor <;> intro h <;> linarith

/-- Case VI, both ends clamped: the equation of case I. -/
theorem case_VI {ω : ℝ} (hω : ω ≠ 0) :
    (∃ v : Fin 4 → ℝ, v ≠ 0 ∧ BC .clamped .clamped (modeV ω v)) ↔ cos ω * cosh ω = 1 := by
  rw [exists_mode_iff hω, det_clamped_clamped]; constructor <;> intro h <;> linarith

/-! ## The roots (§§ 16–17 and 30) -/

theorem hasDerivAt_cos_mul_cosh (x : ℝ) :
    HasDerivAt (fun x => cos x * cosh x) (cos x * sinh x - sin x * cosh x) x :=
  ((hasDerivAt_cos x).mul (hasDerivAt_cosh x)).congr_deriv (by ring)

theorem hasDerivAt_P (x : ℝ) :
    HasDerivAt (fun x => sin x * cosh x - cos x * sinh x) (2 * sin x * sinh x) x :=
  (((hasDerivAt_sin x).mul (hasDerivAt_cosh x)).sub
    ((hasDerivAt_cos x).mul (hasDerivAt_sinh x))).congr_deriv (by ring)

/-- `sin x cosh x - cos x sinh x > 0` on `]0, π]`. -/
theorem P_pos {x : ℝ} (h0 : 0 < x) (h1 : x ≤ π) : 0 < sin x * cosh x - cos x * sinh x := by
  have mono : StrictMonoOn (fun x => sin x * cosh x - cos x * sinh x) (Set.Icc 0 π) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 π)
    · exact (by fun_prop : Continuous fun x => sin x * cosh x - cos x * sinh x).continuousOn
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hasDerivAt_P y).deriv]
      exact mul_pos (mul_pos two_pos (sin_pos_of_pos_of_lt_pi hy.1 hy.2))
        (sinh_pos_iff.mpr hy.1)
  have := mono ⟨le_refl 0, pi_pos.le⟩ ⟨h0.le, h1⟩ h0
  simpa using this

/-- § 16: no root of `cos ω cosh ω = 1` in `]0, 3π/2]`; in fact `cos x cosh x < 1` there. -/
theorem cos_mul_cosh_lt_one {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 3 * π / 2) : cos x * cosh x < 1 := by
  rcases le_or_gt x π with hxπ | hxπ
  · have anti : StrictAntiOn (fun x => cos x * cosh x) (Set.Icc 0 π) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc 0 π)
      · exact (by fun_prop : Continuous fun x => cos x * cosh x).continuousOn
      · intro y hy
        rw [interior_Icc] at hy
        rw [(hasDerivAt_cos_mul_cosh y).deriv]
        have := P_pos hy.1 hy.2.le
        linarith
    have := anti ⟨le_refl 0, pi_pos.le⟩ ⟨h0.le, hxπ⟩ h0
    simpa using this
  · have hc : cos x ≤ 0 :=
      cos_nonpos_of_pi_div_two_le_of_le (by linarith [pi_pos]) (by linarith)
    nlinarith [cosh_pos x]

/-- §§ 16–17: the first positive root of `cos ω cosh ω = 1` is `3π/2 + φ` with
`0 < φ < 1/50`, and it is the only root in `]0, 2π[`. -/
theorem first_root_free_free :
    ∃ ω₁, 3 * π / 2 < ω₁ ∧ ω₁ < 3 * π / 2 + 1 / 50 ∧ cos ω₁ * cosh ω₁ = 1 ∧
      ∀ x, 0 < x → x < 2 * π → cos x * cosh x = 1 → x = ω₁ := by
  have hπ := pi_gt_d6
  have hf0 : cos (3 * π / 2) * cosh (3 * π / 2) = 0 := by
    rw [show 3 * π / 2 = π / 2 + π by ring, cos_add_pi, cos_pi_div_two, neg_zero, zero_mul]
  have hf1 : 1 < cos (3 * π / 2 + 1 / 50) * cosh (3 * π / 2 + 1 / 50) := by
    have hcs : cos (3 * π / 2 + 1 / 50) = sin (1 / 50) := by
      rw [show 3 * π / 2 + 1 / 50 = (1 / 50 + π / 2) + π by ring, cos_add_pi,
        cos_add_pi_div_two, neg_neg]
    rw [hcs]
    have hs : (0.0199 : ℝ) < sin (1 / 50) := by
      have := sin_gt_sub_cube (x := (1 : ℝ) / 50) (by norm_num)
      have h' : (0.0199 : ℝ) < 1 / 50 - (1 / 50) ^ 3 / 6 := by norm_num
      linarith
    have hy : (4.73 : ℝ) ≤ 3 * π / 2 + 1 / 50 := by linarith
    have h4 : exp 1 ^ 4 * exp 0.73 = exp 4.73 := by
      rw [← exp_nat_mul, ← exp_add]; norm_num
    have hq := quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.73 by norm_num)
    have hpow : (2.7182818283 : ℝ) ^ 4 ≤ exp 1 ^ 4 :=
      pow_le_pow_left₀ (by norm_num) exp_one_gt_d9.le 4
    have hE : (108 : ℝ) < exp 4.73 := by
      calc (108 : ℝ) < 2.7182818283 ^ 4 * (1 + 0.73 + 0.73 ^ 2 / 2) := by norm_num
        _ ≤ exp 1 ^ 4 * exp 0.73 := mul_le_mul hpow hq (by norm_num) (by positivity)
        _ = exp 4.73 := h4
    have hcy : (54 : ℝ) < cosh (3 * π / 2 + 1 / 50) := by
      rw [cosh_eq]
      have := exp_le_exp.mpr hy
      have := exp_pos (-(3 * π / 2 + 1 / 50))
      linarith
    have := mul_lt_mul'' hs hcy (by norm_num) (by norm_num)
    linarith
  have hcont : Continuous fun x => cos x * cosh x := by fun_prop
  have hmem : (1 : ℝ) ∈ Set.Ioo (cos (3 * π / 2) * cosh (3 * π / 2))
      (cos (3 * π / 2 + 1 / 50) * cosh (3 * π / 2 + 1 / 50)) := ⟨by rw [hf0]; norm_num, hf1⟩
  obtain ⟨ω₁, ⟨h1, h2⟩, hω₁⟩ := intermediate_value_Ioo (f := fun x => cos x * cosh x)
    (by linarith : 3 * π / 2 ≤ 3 * π / 2 + 1 / 50) hcont.continuousOn hmem
  have mono : StrictMonoOn (fun x => cos x * cosh x) (Set.Icc (3 * π / 2) (2 * π)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont.continuousOn
    intro y hy
    rw [interior_Icc] at hy
    rw [(hasDerivAt_cos_mul_cosh y).deriv]
    have hcos : 0 < cos y := by
      rw [← cos_sub_two_pi]
      exact cos_pos_of_mem_Ioo ⟨by linarith [hy.1], by linarith [hy.2, pi_pos]⟩
    have hsin : sin y < 0 := by
      rw [← sin_sub_two_pi]
      exact sin_neg_of_neg_of_neg_pi_lt (by linarith [hy.2]) (by linarith [hy.1])
    have hy0 : 0 < y := by linarith [hy.1, pi_pos]
    have := mul_pos hcos (sinh_pos_iff.mpr hy0)
    have := mul_pos (neg_pos.mpr hsin) (cosh_pos y)
    linarith
  refine ⟨ω₁, h1, h2, hω₁, fun x hx0 hx1 hx => ?_⟩
  rcases le_or_gt x (3 * π / 2) with hx2 | hx2
  · exact absurd hx (cos_mul_cosh_lt_one hx0 hx2).ne
  · exact mono.injOn ⟨hx2.le, hx1.le⟩ ⟨h1.le, by linarith⟩ (hx.trans hω₁.symm)

/-- § 30: `cos ω cosh ω = -1` has a root in the second quadrant. -/
theorem root_free_clamped : ∃ ω, π / 2 < ω ∧ ω < π ∧ cos ω * cosh ω = -1 := by
  have hcont : Continuous fun x => cos x * cosh x + 1 := by fun_prop
  have ha : cos (π / 2) * cosh (π / 2) + 1 = 1 := by rw [cos_pi_div_two]; ring
  have hb : cos π * cosh π + 1 < 0 := by
    rw [cos_pi]; have := one_lt_cosh.mpr pi_pos.ne'; linarith
  have hmem : (0 : ℝ) ∈ Set.Ioo (cos π * cosh π + 1) (cos (π / 2) * cosh (π / 2) + 1) :=
    ⟨hb, by rw [ha]; norm_num⟩
  obtain ⟨ω, ⟨h1, h2⟩, hω⟩ := intermediate_value_Ioo' (f := fun x => cos x * cosh x + 1)
    (by linarith [pi_pos] : π / 2 ≤ π) hcont.continuousOn hmem
  exact ⟨ω, h1, h2, by simp only at hω; linarith⟩

/-! ## § 47: the lamina supported at both ends and at an intermediate point -/

/-- The right-hand side of Euler's final equation (§ 47), `μ = 1 - l`. -/
noncomputable def eulerFinal (l ω : ℝ) : ℝ :=
  2 - 2 * exp (2 * ω) - (exp (l * ω) - exp ((2 - l) * ω)) * (exp (l * ω) - exp (-(l * ω))) *
    sin ω / (sin (l * ω) * sin ((1 - l) * ω))

private theorem exp_split (l ω : ℝ) :
    exp ω = exp (l * ω) * exp ((1 - l) * ω) ∧
    exp (2 * ω) = exp (l * ω) ^ 2 * exp ((1 - l) * ω) ^ 2 ∧
    exp ((2 - l) * ω) = exp (l * ω) * exp ((1 - l) * ω) ^ 2 ∧
    exp (2 * (l * ω)) = exp (l * ω) ^ 2 ∧
    exp (2 * ((1 - l) * ω)) = exp ((1 - l) * ω) ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← exp_add]; congr 1; ring
  · rw [show 2 * ω = l * ω + l * ω + ((1 - l) * ω + (1 - l) * ω) by ring, exp_add, exp_add,
      exp_add]; ring
  · rw [show (2 - l) * ω = l * ω + ((1 - l) * ω + (1 - l) * ω) by ring, exp_add, exp_add]; ring
  · rw [show 2 * (l * ω) = l * ω + l * ω by ring, exp_add]; ring
  · rw [show 2 * ((1 - l) * ω) = (1 - l) * ω + (1 - l) * ω by ring, exp_add]; ring

/-- Euler's final equation is `sinh ω sin λω sin μω = sin ω sinh λω sinh μω` up to the factor
`-4 e^ω / (sin λω sin μω)`: first multiplied out, … -/
theorem eulerFinal_mul (l ω : ℝ) (hs1 : sin (l * ω) ≠ 0) (hs2 : sin ((1 - l) * ω) ≠ 0) :
    eulerFinal l ω * (sin (l * ω) * sin ((1 - l) * ω)) = -(4 * exp ω * (sinh ω * sin (l * ω) *
      sin ((1 - l) * ω) - sin ω * sinh (l * ω) * sinh ((1 - l) * ω))) := by
  obtain ⟨e1, e2, e3, -, -⟩ := exp_split l ω
  have hA := mul_inv_cancel₀ (exp_pos (l * ω)).ne'
  have hB := mul_inv_cancel₀ (exp_pos ((1 - l) * ω)).ne'
  rw [eulerFinal, sub_mul, div_mul_cancel₀ _ (mul_ne_zero hs1 hs2)]
  simp only [sinh_eq, exp_neg, e2, e3, e1, mul_inv]
  linear_combination (-2 * sin (l * ω) * sin ((1 - l) * ω)) * hA +
    (-2 * sin (l * ω) * sin ((1 - l) * ω) -
      2 * sin (l * ω) * sin ((1 - l) * ω) * (exp (l * ω) * (exp (l * ω))⁻¹ - 1) -
      sin ω * (exp (l * ω) * (exp (l * ω))⁻¹ - exp (l * ω) ^ 2)) * hB

/-- … then divided. -/
theorem eulerFinal_eq (l ω : ℝ) (hs1 : sin (l * ω) ≠ 0) (hs2 : sin ((1 - l) * ω) ≠ 0) :
    eulerFinal l ω = -(4 * exp ω * (sinh ω * sin (l * ω) * sin ((1 - l) * ω) -
      sin ω * sinh (l * ω) * sinh ((1 - l) * ω))) / (sin (l * ω) * sin ((1 - l) * ω)) :=
  eq_div_of_mul_eq (mul_ne_zero hs1 hs2) (eulerFinal_mul l ω hs1 hs2)

/-- The form of the « Remarques », § 2 (view 322), is Euler's equation multiplied by
`sin λω sin μω`. -/
theorem germainForm_eq (l ω : ℝ) :
    2 * (1 - exp (2 * ω)) * sin (l * ω) * sin ((1 - l) * ω) -
        (1 - exp (2 * ((1 - l) * ω))) * (exp (2 * (l * ω)) - 1) * sin ω =
      (2 - 2 * exp (2 * ω)) * sin (l * ω) * sin ((1 - l) * ω) -
        (exp (l * ω) - exp ((2 - l) * ω)) * (exp (l * ω) - exp (-(l * ω))) * sin ω := by
  obtain ⟨-, e2, e3, e4, e5⟩ := exp_split l ω
  have hA := mul_inv_cancel₀ (exp_pos (l * ω)).ne'
  rw [e2, e3, e4, e5, exp_neg]
  linear_combination (-(sin ω) * (1 - exp ((1 - l) * ω) ^ 2)) * hA

/-- § 2 for `λ = 1/n` (`n λ = 1`): the division by `e^{2λω} - 1`, the sum being
`1 + e^{2λω} + … + e^{2(n-1)λω} = 1 + … + e^{2μω}`. -/
theorem germain_geom_form (n : ℕ) (l ω : ℝ) (hl : (n : ℝ) * l = 1) :
    (exp (2 * (l * ω)) - 1) * (2 * (∑ i ∈ Finset.range n, exp (2 * (l * ω)) ^ i) *
        sin (l * ω) * sin ((1 - l) * ω) + (1 - exp (2 * ((1 - l) * ω))) * sin ω) =
      -(2 * (1 - exp (2 * ω)) * sin (l * ω) * sin ((1 - l) * ω) -
        (1 - exp (2 * ((1 - l) * ω))) * (exp (2 * (l * ω)) - 1) * sin ω) := by
  have hgeom := geom_sum_mul (exp (2 * (l * ω))) n
  have hpow : exp (2 * (l * ω)) ^ n = exp (2 * ω) := by
    rw [← exp_nat_mul]; congr 1; linear_combination (2 * ω) * hl
  rw [hpow] at hgeom
  linear_combination (2 * sin (l * ω) * sin ((1 - l) * ω)) * hgeom

/-- The `coth/cot` form of the final equation. -/
theorem final_iff_coth (l ω : ℝ) (h1 : sinh (l * ω) ≠ 0) (h2 : sinh ((1 - l) * ω) ≠ 0)
    (h3 : sin (l * ω) ≠ 0) (h4 : sin ((1 - l) * ω) ≠ 0) :
    sinh ω * sin (l * ω) * sin ((1 - l) * ω) = sin ω * sinh (l * ω) * sinh ((1 - l) * ω) ↔
      cosh (l * ω) / sinh (l * ω) + cosh ((1 - l) * ω) / sinh ((1 - l) * ω) =
        cos (l * ω) / sin (l * ω) + cos ((1 - l) * ω) / sin ((1 - l) * ω) := by
  have e1 : sinh ω = sinh (l * ω) * cosh ((1 - l) * ω) + cosh (l * ω) * sinh ((1 - l) * ω) := by
    rw [← sinh_add]; congr 1; ring
  have e2 : sin ω = sin (l * ω) * cos ((1 - l) * ω) + cos (l * ω) * sin ((1 - l) * ω) := by
    rw [← sin_add]; congr 1; ring
  rw [e1, e2, div_add_div _ _ h1 h2, div_add_div _ _ h3 h4,
    div_eq_div_iff (mul_ne_zero h1 h2) (mul_ne_zero h3 h4)]
  constructor <;> intro h <;> linear_combination h

/-- § 48, `λ = ½`, in the variable `x = ω/2`: the two families. -/
theorem half_factor (x : ℝ) :
    sinh (2 * x) * sin x * sin x - sin (2 * x) * sinh x * sinh x =
      2 * sin x * sinh x * (cosh x * sin x - cos x * sinh x) := by
  rw [sinh_two_mul, sin_two_mul]; ring

/-- Euler's bracket of § 48 is `2 e^{ω/2} (cosh sin − sinh cos)(ω/2)`. -/
theorem euler_half_bracket (x : ℝ) :
    (1 + exp (2 * x)) * sin x - (exp (2 * x) - 1) * cos x =
      2 * exp x * (cosh x * sin x - sinh x * cos x) := by
  have : exp (2 * x) = exp x * exp x := by rw [← exp_add]; ring_nf
  have hx := (exp_pos x).ne'
  rw [this, cosh_eq, sinh_eq, exp_neg]
  field_simp [hx]
  ring

/-- « Remarques » § 1 (view 214): if `tan(ω/2) = tanh(ω/2)` then `sin ω = tanh ω`. -/
theorem objection_sin_eq_tanh (x : ℝ) (h : sin x * cosh x = cos x * sinh x) :
    sin (2 * x) * cosh (2 * x) = sinh (2 * x) := by
  rw [sin_two_mul, cosh_two_mul, sinh_two_mul]
  linear_combination 2 * (cos x * cosh x - sin x * sinh x) * h +
    2 * sinh x * cosh x * sin_sq_add_cos_sq x

/-- … so that the second family is compatible with `sin ω = 0` only for `ω = 0`. -/
theorem objection_sin_zero (x : ℝ) (h : sin x * cosh x = cos x * sinh x)
    (h0 : sin (2 * x) = 0) : x = 0 := by
  have := objection_sin_eq_tanh x h
  rw [h0, zero_mul] at this
  have : 2 * x = 0 := sinh_eq_zero.mp this.symm
  linarith

/-- The eight conditions of § 47 for a lamina supported at both ends and touched by a stylet
at `l`: supported ends, `y = 0` on both sides of the stylet, slope and curvature continuous.
The third derivative is left free: its jump is the force of the stylet (§ 8). -/
abbrev SupportedStylet (l : ℝ) (Y₁ Y₂ : ℝ → ℝ) : Prop :=
  Y₁ 0 = 0 ∧ iteratedDeriv 2 Y₁ 0 = 0 ∧ Y₂ 1 = 0 ∧ iteratedDeriv 2 Y₂ 1 = 0 ∧
    Y₁ l = 0 ∧ Y₂ l = 0 ∧ deriv Y₁ l = deriv Y₂ l ∧ iteratedDeriv 2 Y₁ l = iteratedDeriv 2 Y₂ l

/-- The first half of the second family: `sinh ωu / sinh(ω/2) − sin ωu / sin(ω/2)`. -/
noncomputable def secondY₁ (ω : ℝ) : ℝ → ℝ :=
  modeY ω 0 (1 / sinh (ω / 2)) 0 (-(1 / sin (ω / 2)))

/-- Its mirror image on the second half. -/
noncomputable def secondY₂ (ω : ℝ) : ℝ → ℝ :=
  reflY ω 0 (1 / sinh (ω / 2)) 0 (-(1 / sin (ω / 2))) 1

/-- **Against the « Remarques ».** Euler's second solution (§ 51) is a genuine motion: for
every root `ω > 0` of `tan(ω/2) = tanh(ω/2)`, the two halves above satisfy the eight
conditions of § 47, do not vanish, and `y'''` jumps at the stylet, which therefore exerts a
force. -/
theorem second_family_is_mode {ω : ℝ} (hω : 0 < ω)
    (h : sin (ω / 2) * cosh (ω / 2) = cos (ω / 2) * sinh (ω / 2)) :
    SupportedStylet (1 / 2) (secondY₁ ω) (secondY₂ ω) ∧ secondY₁ ω ≠ 0 ∧
      iteratedDeriv 3 (secondY₁ ω) (1 / 2) ≠ iteratedDeriv 3 (secondY₂ ω) (1 / 2) := by
  have hx : 0 < ω / 2 := by positivity
  have hshp : 0 < sinh (ω / 2) := sinh_pos_iff.mpr hx
  have hsh : sinh (ω / 2) ≠ 0 := hshp.ne'
  have hsi : sin (ω / 2) ≠ 0 := by
    intro h0
    have hc : cos (ω / 2) * sinh (ω / 2) = 0 := by rw [← h, h0, zero_mul]
    have hc' : cos (ω / 2) = 0 := (mul_eq_zero.mp hc).resolve_right hsh
    have := sin_sq_add_cos_sq (ω / 2)
    rw [h0, hc'] at this; norm_num at this
  have key : cosh (ω / 2) / sinh (ω / 2) - cos (ω / 2) / sin (ω / 2) = 0 := by
    rw [div_sub_div _ _ hsh hsi, div_eq_zero_iff]; left; linear_combination h
  have hm : ω * (1 / 2) = ω / 2 := by ring
  have hm' : ω * (1 - 1 / 2) = ω / 2 := by ring
  have hz : ω * (1 - 1) = 0 := by ring
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [secondY₁, modeY]
  · rw [secondY₁, iteratedDeriv_two_modeY_apply]; simp
  · rw [secondY₂, reflY_apply, hz]; simp
  · rw [secondY₂, iteratedDeriv_two_reflY_apply, hz]; simp
  · rw [secondY₁, modeY_apply, hm]
    linear_combination one_div_mul_cancel hsh - one_div_mul_cancel hsi
  · rw [secondY₂, reflY_apply, hm']
    linear_combination one_div_mul_cancel hsh - one_div_mul_cancel hsi
  · rw [secondY₁, secondY₂, deriv_modeY_apply, deriv_reflY_apply, hm, hm']
    linear_combination 2 * ω * key
  · rw [secondY₁, secondY₂, iteratedDeriv_two_modeY_apply, iteratedDeriv_two_reflY_apply,
      hm, hm']
    ring
  · intro h0
    rw [secondY₁, modeY_eq_zero_iff hω.ne'] at h0
    exact one_div_ne_zero hsh h0.2.1
  · rw [secondY₁, secondY₂, iteratedDeriv_three_modeY_apply, iteratedDeriv_three_reflY_apply,
      hm, hm']
    intro heq
    have h3 : ω ^ 3 * (1 / sinh (ω / 2) * cosh (ω / 2) + 0 * sinh (ω / 2) -
        -(1 / sin (ω / 2)) * cos (ω / 2) + 0 * sin (ω / 2)) =
        ω ^ 3 * (2 * (cosh (ω / 2) / sinh (ω / 2))) := by
      linear_combination (-(ω ^ 3)) * key
    have hpos : 0 < ω ^ 3 * (2 * (cosh (ω / 2) / sinh (ω / 2))) :=
      mul_pos (pow_pos hω 3) (mul_pos two_pos (div_pos (cosh_pos _) hshp))
    linarith

/-- **§ 50, Euler's sign.** For `ω = 2iπ` (first family) the coefficients `(γ, γ') = (1, 1)`
satisfy the eight conditions, with `y'''` continuous (no force at the stylet), while
`(γ, γ') = (1, -1)`, Euler's printed `γ' = -γ` with the same abscissa on both portions,
breaks the continuity of the slope at the stylet. -/
theorem first_family_sign (i : ℤ) (hi : i ≠ 0) :
    SupportedStylet (1 / 2) (modeY (2 * i * π) 0 0 0 1) (modeY (2 * i * π) 0 0 0 1) ∧
      deriv (modeY (2 * i * π) 0 0 0 1) (1 / 2) ≠ deriv (modeY (2 * i * π) 0 0 0 (-1)) (1 / 2) := by
  have s1 : sin (2 * i * π * 1) = 0 := by
    rw [show (2 * i * π * 1 : ℝ) = ((2 * i : ℤ) : ℝ) * π by push_cast; ring]
    exact sin_int_mul_pi _
  have s2 : sin (2 * i * π * (1 / 2)) = 0 := by
    rw [show (2 * i * π * (1 / 2) : ℝ) = (i : ℝ) * π by ring]
    exact sin_int_mul_pi _
  have hc : cos (2 * i * π * (1 / 2)) ≠ 0 := by
    intro h0
    have := sin_sq_add_cos_sq (2 * i * π * (1 / 2))
    rw [s2, h0] at this; norm_num at this
  have hω : (2 * i * π : ℝ) ≠ 0 := by
    have : (i : ℝ) ≠ 0 := by exact_mod_cast hi
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) pi_ne_zero
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [modeY]
  · rw [iteratedDeriv_two_modeY_apply]; simp
  · rw [modeY_apply, s1]; simp
  · rw [iteratedDeriv_two_modeY_apply, s1]; simp
  · rw [modeY_apply, s2]; simp
  · rw [modeY_apply, s2]; simp
  · rw [deriv_modeY_apply, deriv_modeY_apply]
    intro h0
    have : 2 * ((2 * i * π) * cos (2 * i * π * (1 / 2))) = 0 := by linear_combination h0
    rcases mul_eq_zero.mp this with h | h
    · norm_num at h
    · exact (mul_ne_zero hω hc) h

/-- Modes without force at the stylet, `sin(kπu)` with a node at `l` (« points de repos
sympathiques »), exist only at rational positions of the stylet, and at every rational one. -/
theorem sympathetic_iff_rational (l : ℝ) :
    (∃ k : ℕ, 0 < k ∧ sin (k * π * l) = 0) ↔ ∃ q : ℚ, (q : ℝ) = l := by
  constructor
  · rintro ⟨k, hk, h⟩
    obtain ⟨n, hn⟩ := sin_eq_zero_iff.mp h
    refine ⟨(n : ℚ) / k, ?_⟩
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    push_cast
    field_simp
    have := pi_ne_zero
    apply mul_right_cancel₀ this
    linarith
  · rintro ⟨q, rfl⟩
    refine ⟨q.den, q.den_pos, ?_⟩
    have h : (q.den : ℝ) * (q : ℝ) = (q.num : ℝ) := by exact_mod_cast Rat.den_mul_eq_num q
    rw [show (q.den : ℝ) * π * q = (q.num : ℝ) * π by rw [← h]; ring]
    exact sin_int_mul_pi _

/-- « Remarques » § 5: with `λ = 1/λ'` and `m = λ' - 1`, a common term of the two series of
sounds, `(4k+1)² / λ²` and `(4j+1)² / μ²`, asks `(4k+1) m = 4j+1`, which holds for some
`k, j` iff `m ≡ 1 (mod 4)`; none when `m` is even or of the form `4n + 3`. -/
theorem common_term_iff (m : ℤ) : (∃ k j : ℤ, (4 * k + 1) * m = 4 * j + 1) ↔ m % 4 = 1 := by
  constructor
  · rintro ⟨k, j, h⟩
    have h' : m = 4 * (j - k * m) + 1 := by linear_combination h
    generalize k * m = t at h'
    omega
  · intro h
    exact ⟨0, m / 4, by norm_num; omega⟩

/-! ## § 8: the free lamina touched by a stylet at an arbitrary point -/

/-- `P(t) = cosh t sin t − sinh t cos t`; `P = 0` is `tan t = tanh t`. -/
noncomputable def Pf (t : ℝ) : ℝ := cosh t * sin t - sinh t * cos t

/-- `C₊(t) = 1 + cosh t cos t`; `C₊ = 0` is case III. -/
noncomputable def Cplus (t : ℝ) : ℝ := 1 + cosh t * cos t

/-- The eight conditions of § 8: both ends free, `y = 0` on both sides of the stylet at `l`,
slope and curvature continuous there. -/
abbrev FreeStylet (l : ℝ) (Y₁ Y₂ : ℝ → ℝ) : Prop :=
  iteratedDeriv 2 Y₁ 0 = 0 ∧ iteratedDeriv 3 Y₁ 0 = 0 ∧
    iteratedDeriv 2 Y₂ 1 = 0 ∧ iteratedDeriv 3 Y₂ 1 = 0 ∧
    Y₁ l = 0 ∧ Y₂ l = 0 ∧ deriv Y₁ l = deriv Y₂ l ∧ iteratedDeriv 2 Y₁ l = iteratedDeriv 2 Y₂ l

theorem cosh_add_cos_pos {t : ℝ} (ht : t ≠ 0) : 0 < cosh t + cos t := by
  have := one_lt_cosh.mpr ht
  have := neg_one_le_cos t
  linarith

/-- For `t ≠ 0`, `C₊(t)` and `P(t)` do not vanish together. -/
theorem not_both {t : ℝ} (ht : t ≠ 0) : ¬(Cplus t = 0 ∧ Pf t = 0) := by
  rintro ⟨hC, hP⟩
  simp only [Cplus, Pf] at hC hP
  have s1 : (cosh t * sin t) ^ 2 = (sinh t * cos t) ^ 2 := by
    rw [show cosh t * sin t = sinh t * cos t by linear_combination hP]
  have s2 : cosh t ^ 2 = sinh t ^ 2 * cos t ^ 2 + (cosh t * cos t) ^ 2 := by
    linear_combination s1 - cosh t ^ 2 * sin_sq_add_cos_sq t
  have s3 : cosh t ^ 2 = sinh t ^ 2 * cos t ^ 2 + 1 := by
    linear_combination s2 + (cosh t * cos t - 1) * hC
  have s4 : cosh t ^ 4 = sinh t ^ 2 + cosh t ^ 2 := by
    linear_combination cosh t ^ 2 * s3 + sinh t ^ 2 * (cosh t * cos t - 1) * hC
  have s5 : (cosh t ^ 2 - 1) ^ 2 = 0 := by linear_combination s4 - cosh_sq t
  have s6 : sinh t ^ 2 = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp s5
    linear_combination -(cosh_sq t) + this
  exact ht (sinh_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp s6))

/-- The algebraic core of the elimination, forward. -/
theorem core_forward {ch sh co si ch' sh' co' si' a b a' b' : ℝ}
    (i1 : ch ^ 2 = sh ^ 2 + 1) (i2 : si ^ 2 + co ^ 2 = 1)
    (i1' : ch' ^ 2 = sh' ^ 2 + 1) (i2' : si' ^ 2 + co' ^ 2 = 1)
    (hX : 0 < ch + co) (hX' : 0 < ch' + co')
    (E1 : a * ch + b * sh + a * co + b * si = 0)
    (E1' : a' * ch' + b' * sh' + a' * co' + b' * si' = 0)
    (E2 : (b * ch + a * sh + b * co - a * si) + (b' * ch' + a' * sh' + b' * co' - a' * si') = 0)
    (E3 : (a * ch + b * sh - a * co - b * si) - (a' * ch' + b' * sh' - a' * co' - b' * si') = 0)
    (hne : ¬(a = 0 ∧ b = 0 ∧ a' = 0 ∧ b' = 0)) :
    (1 + ch' * co') * (ch * si - sh * co) + (1 + ch * co) * (ch' * si' - sh' * co') = 0 := by
  have k1 : (ch + co) * (b * ch + a * sh + b * co - a * si) = 2 * b * (1 + ch * co) := by
    linear_combination (sh - si) * E1 + b * i1 + b * i2
  have k2 : (ch + co) * (a * ch + b * sh - a * co - b * si) = -2 * b * (ch * si - sh * co) := by
    linear_combination (ch - co) * E1
  have k1' : (ch' + co') * (b' * ch' + a' * sh' + b' * co' - a' * si') =
      2 * b' * (1 + ch' * co') := by
    linear_combination (sh' - si') * E1' + b' * i1' + b' * i2'
  have k2' : (ch' + co') * (a' * ch' + b' * sh' - a' * co' - b' * si') =
      -2 * b' * (ch' * si' - sh' * co') := by
    linear_combination (ch' - co') * E1'
  have s1 : b * (1 + ch * co) * (ch' + co') + b' * (1 + ch' * co') * (ch + co) = 0 := by
    linear_combination ((ch + co) * (ch' + co') / 2) * E2 - ((ch' + co') / 2) * k1 -
      ((ch + co) / 2) * k1'
  have s2 :
      b * (ch * si - sh * co) * (ch' + co') - b' * (ch' * si' - sh' * co') * (ch + co) = 0 := by
    linear_combination (-(ch + co) * (ch' + co') / 2) * E3 + ((ch' + co') / 2) * k2 -
      ((ch + co) / 2) * k2'
  have s3 : b * (ch' + co') *
      ((1 + ch' * co') * (ch * si - sh * co) + (1 + ch * co) * (ch' * si' - sh' * co')) = 0 := by
    linear_combination (1 + ch' * co') * s2 + (ch' * si' - sh' * co') * s1
  have s4 : b' * (ch + co) *
      ((1 + ch' * co') * (ch * si - sh * co) + (1 + ch * co) * (ch' * si' - sh' * co')) = 0 := by
    linear_combination (ch * si - sh * co) * s1 - (1 + ch * co) * s2
  by_cases hb : b = 0
  · by_cases hb' : b' = 0
    · exfalso; apply hne
      subst hb hb'
      have ha : a * (ch + co) = 0 := by linear_combination E1
      have ha' : a' * (ch' + co') = 0 := by linear_combination E1'
      exact ⟨(mul_eq_zero.mp ha).resolve_right hX.ne', rfl,
        (mul_eq_zero.mp ha').resolve_right hX'.ne', rfl⟩
    · exact (mul_eq_zero.mp s4).resolve_left (mul_ne_zero hb' hX.ne')
  · exact (mul_eq_zero.mp s3).resolve_left (mul_ne_zero hb hX'.ne')

/-- The algebraic core of the elimination, backward. -/
theorem core_backward {ch sh co si ch' sh' co' si' : ℝ}
    (i1 : ch ^ 2 = sh ^ 2 + 1) (i2 : si ^ 2 + co ^ 2 = 1)
    (i1' : ch' ^ 2 = sh' ^ 2 + 1) (i2' : si' ^ 2 + co' ^ 2 = 1)
    (hX : 0 < ch + co) (hnb : ¬(1 + ch' * co' = 0 ∧ ch' * si' - sh' * co' = 0))
    (hG : (1 + ch' * co') * (ch * si - sh * co) + (1 + ch * co) * (ch' * si' - sh' * co') = 0) :
    ∃ a b a' b' : ℝ, b ≠ 0 ∧ a * ch + b * sh + a * co + b * si = 0 ∧
      a' * ch' + b' * sh' + a' * co' + b' * si' = 0 ∧
      (b * ch + a * sh + b * co - a * si) + (b' * ch' + a' * sh' + b' * co' - a' * si') = 0 ∧
      (a * ch + b * sh - a * co - b * si) - (a' * ch' + b' * sh' - a' * co' - b' * si') = 0 := by
  have : ∃ B B' : ℝ, B ≠ 0 ∧ B * (1 + ch * co) + B' * (1 + ch' * co') = 0 ∧
      B * (ch * si - sh * co) - B' * (ch' * si' - sh' * co') = 0 := by
    by_cases hC : 1 + ch' * co' = 0
    · have hP : ch' * si' - sh' * co' ≠ 0 := fun hP => hnb ⟨hC, hP⟩
      exact ⟨ch' * si' - sh' * co', ch * si - sh * co, hP, by linear_combination hG, by ring⟩
    · exact ⟨1 + ch' * co', -(1 + ch * co), hC, by ring, by linear_combination hG⟩
  obtain ⟨B, B', hB, hB1, hB2⟩ := this
  refine ⟨-B * (sh + si), B * (ch + co), -B' * (sh' + si'), B' * (ch' + co'),
    mul_ne_zero hB hX.ne', by ring, by ring, ?_, ?_⟩
  · linear_combination 2 * hB1 + B * i1 + B * i2 + B' * i1' + B' * i2'
  · linear_combination (-2) * hB2

/-- **§ 8, view 342.** The lamina free at both ends, touched by a stylet at `l`
(`0 < l < 1`): a motion not identically zero satisfying the eight conditions exists iff
`C₊(μω) P(λω) + C₊(λω) P(μω) = 0`, `μ = 1 - λ`, the equation of the leaf. -/
theorem free_stylet_iff {ω l : ℝ} (hω : 0 < ω) (hl0 : 0 < l) (hl1 : l < 1) :
    (∃ a b c d a' b' c' d' : ℝ, (modeY ω a b c d ≠ 0 ∨ reflY ω a' b' c' d' 1 ≠ 0) ∧
      FreeStylet l (modeY ω a b c d) (reflY ω a' b' c' d' 1)) ↔
    Cplus (ω * (1 - l)) * Pf (ω * l) + Cplus (ω * l) * Pf (ω * (1 - l)) = 0 := by
  have ht : ω * l ≠ 0 := (mul_pos hω hl0).ne'
  have ht' : ω * (1 - l) ≠ 0 := (mul_pos hω (by linarith)).ne'
  have hz : ω * 0 = 0 := mul_zero ω
  have hz' : ω * (1 - 1) = 0 := by ring
  simp only [Cplus, Pf]
  constructor
  · rintro ⟨a, b, c, d, a', b', c', d', hne, h1, h2, h3, h4, h5, h6, h7, h8⟩
    rw [iteratedDeriv_two_modeY_apply, hz, cosh_zero, sinh_zero, cos_zero, sin_zero] at h1
    rw [iteratedDeriv_three_modeY_apply, hz, cosh_zero, sinh_zero, cos_zero, sin_zero] at h2
    rw [iteratedDeriv_two_reflY_apply, hz', cosh_zero, sinh_zero, cos_zero, sin_zero] at h3
    rw [iteratedDeriv_three_reflY_apply, hz', cosh_zero, sinh_zero, cos_zero, sin_zero] at h4
    rw [modeY_apply] at h5
    rw [reflY_apply] at h6
    rw [deriv_modeY_apply, deriv_reflY_apply] at h7
    rw [iteratedDeriv_two_modeY_apply, iteratedDeriv_two_reflY_apply] at h8
    have hc : c = a := by
      have := (mul_eq_zero.mp h1).resolve_left (pow_ne_zero 2 hω.ne'); linarith
    have hd : d = b := by
      have := (mul_eq_zero.mp h2).resolve_left (pow_ne_zero 3 hω.ne'); linarith
    have hc' : c' = a' := by
      have := (mul_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left one_ne_zero)).resolve_left
        (pow_ne_zero 2 hω.ne')
      linarith
    have hd' : d' = b' := by
      have := (mul_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left (by norm_num))).resolve_left
        (pow_ne_zero 3 hω.ne')
      linarith
    rw [hc, hd] at h5 h7 h8 hne
    rw [hc', hd'] at h6 h7 h8 hne
    have E2 : ω * ((b * cosh (ω * l) + a * sinh (ω * l) + b * cos (ω * l) - a * sin (ω * l)) +
        (b' * cosh (ω * (1 - l)) + a' * sinh (ω * (1 - l)) + b' * cos (ω * (1 - l)) -
          a' * sin (ω * (1 - l)))) = 0 := by
      linear_combination h7
    have E3 : ω ^ 2 * ((a * cosh (ω * l) + b * sinh (ω * l) - a * cos (ω * l) - b * sin (ω * l)) -
        (a' * cosh (ω * (1 - l)) + b' * sinh (ω * (1 - l)) - a' * cos (ω * (1 - l)) -
          b' * sin (ω * (1 - l)))) = 0 := by
      linear_combination h8
    refine core_forward (cosh_sq _) (sin_sq_add_cos_sq _) (cosh_sq _) (sin_sq_add_cos_sq _)
      (cosh_add_cos_pos ht) (cosh_add_cos_pos ht') h5 (by linear_combination h6)
      ((mul_eq_zero.mp E2).resolve_left hω.ne')
      ((mul_eq_zero.mp E3).resolve_left (pow_ne_zero 2 hω.ne')) ?_
    rintro ⟨rfl, rfl, rfl, rfl⟩
    rcases hne with h | h
    · exact h (by funext u; simp [modeY])
    · exact h (by funext u; simp [reflY, modeY])
  · intro hG
    have hnb := not_both ht'
    simp only [Cplus, Pf] at hnb
    obtain ⟨a, b, a', b', hb, E1, E1', E2, E3⟩ :=
      core_backward (cosh_sq _) (sin_sq_add_cos_sq _) (cosh_sq _) (sin_sq_add_cos_sq _)
        (cosh_add_cos_pos ht) hnb hG
    refine ⟨a, b, a, b, a', b', a', b', Or.inl ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h; rw [modeY_eq_zero_iff hω.ne'] at h; exact hb h.2.1
    · rw [iteratedDeriv_two_modeY_apply, hz, cosh_zero, sinh_zero, cos_zero, sin_zero]; ring
    · rw [iteratedDeriv_three_modeY_apply, hz, cosh_zero, sinh_zero, cos_zero, sin_zero]; ring
    · rw [iteratedDeriv_two_reflY_apply, hz', cosh_zero, sinh_zero, cos_zero, sin_zero]; ring
    · rw [iteratedDeriv_three_reflY_apply, hz', cosh_zero, sinh_zero, cos_zero, sin_zero]; ring
    · rw [modeY_apply]; linear_combination E1
    · rw [reflY_apply]; linear_combination E1'
    · rw [deriv_modeY_apply, deriv_reflY_apply]; linear_combination ω * E2
    · rw [iteratedDeriv_two_modeY_apply, iteratedDeriv_two_reflY_apply]
      linear_combination ω ^ 2 * E3

/-- **§ 9, against the leaf.** With the stylet at the middle, every root of `C₊(ω/2) = 0`
gives a genuine motion of the free lamina touched by the stylet. -/
theorem free_stylet_half {ω : ℝ} (hω : 0 < ω) (h : Cplus (ω / 2) = 0) :
    ∃ a b c d a' b' c' d' : ℝ, (modeY ω a b c d ≠ 0 ∨ reflY ω a' b' c' d' 1 ≠ 0) ∧
      FreeStylet (1 / 2) (modeY ω a b c d) (reflY ω a' b' c' d' 1) := by
  apply (free_stylet_iff hω (by norm_num) (by norm_num)).mpr
  rw [show ω * (1 - 1 / 2) = ω / 2 by ring, show ω * (1 / 2) = ω / 2 by ring, h]
  ring

/-- **§ 9.** What the leaf proves is right: `C₊(x) = 0` and `cos 2x cosh 2x = 1` are
incompatible for `x ≠ 0`; these motions are not motions of the free lamina without stylet. -/
theorem cplus_incompatible {x : ℝ} (hx : x ≠ 0) (h : Cplus x = 0) :
    cos (2 * x) * cosh (2 * x) ≠ 1 := by
  intro h2
  simp only [Cplus] at h
  rw [cos_two_mul, cosh_two_mul] at h2
  have s : (cosh x ^ 2 - 1) ^ 2 = 0 := by
    linear_combination (-(cosh x) ^ 2 / 2) * h2 +
      (-(cosh x) ^ 2 / 2) * (2 * cos x ^ 2 - 1) * cosh_sq x +
      (2 * cosh x ^ 2 - 1) * (cosh x * cos x - 1) * h
  have s' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp s
  have s'' : sinh x ^ 2 = 0 := by linear_combination -(cosh_sq x) + s'
  exact hx (sinh_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp s''))

/-! ## The plate: the memoir for the Institut, §§ 1–2 -/

/-- (B) can be lowered to the second degree (view 404): for a linear operator `L` (the
Laplacian on smooth functions), a solution of `h² L z = ± z` solves `h⁴ L² z = z`. -/
theorem factor_B_left {V : Type*} [AddCommGroup V] [Module ℝ V] (L : V →ₗ[ℝ] V) (h : ℝ)
    (z : V) (hz : h ^ 2 • L z = z ∨ h ^ 2 • L z = -z) : h ^ 4 • L (L z) = z := by
  have e : h ^ 4 • L (L z) = h ^ 2 • L (h ^ 2 • L z) := by
    rw [map_smul, smul_smul]; congr 1; ring
  rcases hz with hz | hz
  · rw [e, hz, hz]
  · rw [e, hz, map_neg, smul_neg, hz, neg_neg]

/-- … and every solution of (B) is the sum of one of each (used at view 436). -/
theorem factor_B_split {V : Type*} [AddCommGroup V] [Module ℝ V] (L : V →ₗ[ℝ] V) (h : ℝ)
    (z : V) (hz : h ^ 4 • L (L z) = z) :
    z = (1 / 2 : ℝ) • (z + h ^ 2 • L z) + (1 / 2 : ℝ) • (z - h ^ 2 • L z) ∧
      h ^ 2 • L ((1 / 2 : ℝ) • (z + h ^ 2 • L z)) = (1 / 2 : ℝ) • (z + h ^ 2 • L z) ∧
      h ^ 2 • L ((1 / 2 : ℝ) • (z - h ^ 2 • L z)) = -((1 / 2 : ℝ) • (z - h ^ 2 • L z)) := by
  refine ⟨by module, ?_, ?_⟩
  · simp only [map_smul, map_add]
    linear_combination (norm := module) (1 / 2 : ℝ) • hz
  · simp only [map_smul, map_sub]
    linear_combination (norm := module) (-(1 / 2 : ℝ)) • hz

/-- The partial derivative in `x` of a function of `(x, y)`. -/
noncomputable def dx (z : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun x y => deriv (fun x' => z x' y) x
/-- The partial derivative in `y` of a function of `(x, y)`. -/
noncomputable def dy (z : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun x y => deriv (fun y' => z x y') y
/-- The Laplacian of a function of `(x, y)`. -/
noncomputable def lap (z : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun x y => dx (dx z) x y + dy (dy z) x y

theorem lap_sep (F G F' G' F'' G'' : ℝ → ℝ) (hF : ∀ x, HasDerivAt F (F' x) x)
    (hF' : ∀ x, HasDerivAt F' (F'' x) x) (hG : ∀ y, HasDerivAt G (G' y) y)
    (hG' : ∀ y, HasDerivAt G' (G'' y) y) :
    lap (fun x y => F x + G y) = fun x y => F'' x + G'' y := by
  funext x y
  have h1 : (fun x' => deriv (fun x'' => F x'' + G y) x') = F' :=
    funext fun x' => ((hF x').add_const (G y)).deriv
  have h2 : (fun y' => deriv (fun y'' => F x + G y'') y') = G' :=
    funext fun y' => ((hG y').const_add (F x)).deriv
  change deriv (fun x' => deriv (fun x'' => F x'' + G y) x') x +
    deriv (fun y' => deriv (fun y'' => F x + G y'') y') y = F'' x + G'' y
  rw [h1, h2, (hF' x).deriv, (hG' y).deriv]

theorem lap_prod (F G F' G' F'' G'' : ℝ → ℝ) (hF : ∀ x, HasDerivAt F (F' x) x)
    (hF' : ∀ x, HasDerivAt F' (F'' x) x) (hG : ∀ y, HasDerivAt G (G' y) y)
    (hG' : ∀ y, HasDerivAt G' (G'' y) y) :
    lap (fun x y => F x * G y) = fun x y => F'' x * G y + F x * G'' y := by
  funext x y
  have h1 : (fun x' => deriv (fun x'' => F x'' * G y) x') = fun x' => F' x' * G y :=
    funext fun x' => ((hF x').mul_const (G y)).deriv
  have h2 : (fun y' => deriv (fun y'' => F x * G y'') y') = fun y' => F x * G' y' :=
    funext fun y' => ((hG y').const_mul (F x)).deriv
  change deriv (fun x' => deriv (fun x'' => F x'' * G y) x') x +
    deriv (fun y' => deriv (fun y'' => F x * G y'') y') y = F'' x * G y + F x * G'' y
  rw [h1, h2, ((hF' x).mul_const (G y)).deriv, ((hG' y).const_mul (F x)).deriv]

theorem lap_modeY_sum (k a b c d a' b' c' d' : ℝ) :
    lap (fun x y => modeY k a b c d x + modeY k a' b' c' d' y) = fun x y =>
      modeY k (k * (k * a)) (k * (k * b)) (k * (-(k * c))) (-(k * (k * d))) x +
      modeY k (k * (k * a')) (k * (k * b')) (k * (-(k * c'))) (-(k * (k * d'))) y :=
  lap_sep _ _ _ _ _ _ (hasDerivAt_modeY k a b c d) (hasDerivAt_modeY k _ _ _ _)
    (hasDerivAt_modeY k a' b' c' d') (hasDerivAt_modeY k _ _ _ _)

theorem lap_modeY_prod (α β a b c d a' b' c' d' : ℝ) :
    lap (fun x y => modeY α a b c d x * modeY β a' b' c' d' y) = fun x y =>
      modeY α (α * (α * a)) (α * (α * b)) (α * (-(α * c))) (-(α * (α * d))) x *
        modeY β a' b' c' d' y +
      modeY α a b c d x *
        modeY β (β * (β * a')) (β * (β * b')) (β * (-(β * c'))) (-(β * (β * d'))) y :=
  lap_prod _ _ _ _ _ _ (hasDerivAt_modeY α a b c d) (hasDerivAt_modeY α _ _ _ _)
    (hasDerivAt_modeY β a' b' c' d') (hasDerivAt_modeY β _ _ _ _)

/-- **The integral (C)** (view 405): `z = f(x) + g(y)` with `f, g` of Euler's form of
reduced length `k = ω/A` satisfies `Δ² z = k⁴ z`, hence (B) when `K b τ² k⁴ = 1`. -/
theorem plate_C (k a b c d a' b' c' d' : ℝ) :
    lap (lap (fun x y => modeY k a b c d x + modeY k a' b' c' d' y)) =
      fun x y => k ^ 4 * (modeY k a b c d x + modeY k a' b' c' d' y) := by
  rw [lap_modeY_sum, lap_modeY_sum]
  funext x y; simp only [modeY]; ring

/-- **The integral (D)** (view 406): `z = sin(πnx/A) sin(πmy/A)` has
`Δz = -(α² + β²) z` and `Δ²z = (α² + β²)² z`, `α = πn/A`, `β = πm/A`. -/
theorem plate_D (α β : ℝ) :
    lap (fun x y => sin (α * x) * sin (β * y)) =
        (fun x y => -(α ^ 2 + β ^ 2) * (sin (α * x) * sin (β * y))) ∧
      lap (lap (fun x y => sin (α * x) * sin (β * y))) =
        (fun x y => (α ^ 2 + β ^ 2) ^ 2 * (sin (α * x) * sin (β * y))) := by
  have hz : (fun x y => sin (α * x) * sin (β * y)) =
      fun x y => modeY α 0 0 0 1 x * modeY β 0 0 0 1 y := by
    funext x y; simp [modeY]
  have hl : lap (fun x y => sin (α * x) * sin (β * y)) =
      fun x y => modeY α 0 0 0 (-(α ^ 2 + β ^ 2)) x * modeY β 0 0 0 1 y := by
    rw [hz, lap_modeY_prod]; funext x y; simp only [modeY]; ring
  refine ⟨?_, ?_⟩
  · rw [hl]; funext x y; simp only [modeY]; ring
  · rw [hl, lap_modeY_prod]; funext x y; simp only [modeY]; ring

/-- (D) vanishes on the four sides of the square `[0, A]²` when `n, m` are integers, and by
`plate_D` so does its Laplacian: it is a mode of the square plate supported on its contour. -/
theorem plate_D_boundary (n m : ℤ) {A : ℝ} (hA : A ≠ 0) (x y : ℝ) :
    sin (π * n / A * 0) * sin (π * m / A * y) = 0 ∧
      sin (π * n / A * A) * sin (π * m / A * y) = 0 ∧
      sin (π * n / A * x) * sin (π * m / A * 0) = 0 ∧
      sin (π * n / A * x) * sin (π * m / A * A) = 0 := by
  have h1 : sin (π * n / A * A) = 0 := by
    rw [div_mul_cancel₀ _ hA, mul_comm]; exact sin_int_mul_pi n
  have h2 : sin (π * m / A * A) = 0 := by
    rw [div_mul_cancel₀ _ hA, mul_comm]; exact sin_int_mul_pi m
  refine ⟨by simp, by rw [h1, zero_mul], by simp, by rw [h2, mul_zero]⟩

/-- The sound of (D): if `K b τ² (α² + β²)² = 1`, then `√(1/K)/π = π (m² + n²) τ √b / A²`,
the formula of view 406. -/
theorem plate_D_sound {K b τ A n m : ℝ} (hτ : 0 < τ) (hA : A ≠ 0)
    (hK : K * b * τ ^ 2 * ((π * n / A) ^ 2 + (π * m / A) ^ 2) ^ 2 = 1) :
    √(1 / K) / π = π * (m ^ 2 + n ^ 2) * τ * √b / A ^ 2 := by
  have hs0 : 0 ≤ (π * n / A) ^ 2 + (π * m / A) ^ 2 := by positivity
  have hK0 : K ≠ 0 := by rintro rfl; simp at hK
  have hπ := pi_ne_zero
  have h1 : 1 / K = (τ * ((π * n / A) ^ 2 + (π * m / A) ^ 2)) ^ 2 * b := by
    rw [div_eq_iff hK0]; linear_combination (-1 : ℝ) * hK
  rw [h1, sqrt_mul (by positivity), sqrt_sq (mul_nonneg hτ.le hs0)]
  field_simp [hπ, hA]
  ring

end LeanPool.SophieGermainArchives.Fr9115Elasticity
