/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P3776T1DiskMapExponentialLift

-- [TABLET NODE: P3776T1BoundedDisplacementSurjective]

/-!
# P3776T1BoundedDisplacementSurjective

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace BoundedDisplacementConstruction

private theorem hmiss (f : ℝ × ℝ → ℝ × ℝ) (y : ℝ × ℝ) (hnot : ¬∃ a, f a = y) : ∀ x, f x ≠ y := by
  classical
  simpa [Function.Surjective] using hnot

private noncomputable abbrev pc : (Real × Real) → ℂ := by
  classical
  exact fun x => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I

private noncomputable abbrev R (M : ℝ) : Real := by
  classical
  exact 2 * M + 1

private theorem hR (M : ℝ) (hM : 0 ≤ M) : 0 ≤ (R M) := by
  classical
  let R : Real := 2 * M + 1
  change (0 ≤ R)
  dsimp [R]; linarith

private theorem hRpos (M : ℝ) (hM : 0 ≤ M) : 0 < (R M) := by
  classical
  let R : Real := 2 * M + 1
  change (0 < R)
  dsimp [R]; linarith

private theorem hMR (M : ℝ) : 2 * M < (R M) := by
  classical
  let R : Real := 2 * M + 1
  change (2 * M < R)
  dsimp [R]; linarith

private noncomputable abbrev D (M : ℝ) (y : ℝ × ℝ) : Set (ℝ × ℝ) := by
  classical
  let R : Real := 2 * M + 1
  exact Metric.closedBall y R

private noncomputable abbrev g (f : ℝ × ℝ → ℝ × ℝ) (hf : Continuous f) (M : ℝ) (y : ℝ × ℝ) : C((D
    M y), ℂ) := by
  classical
  let pc : (Real × Real) → ℂ := fun x => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I
  let R : Real := 2 * M + 1
  let D := Metric.closedBall y R
  change (C(D, ℂ))
  exact ⟨fun x => pc (f x) - pc y, by fun_prop⟩

private theorem hg (f : ℝ × ℝ → ℝ × ℝ) (hf : Continuous f) (M : ℝ) (y : ℝ × ℝ) (hmiss : ∀ (x : ℝ
    × ℝ), f x ≠ y) : ∀ x, (g f hf M y) x ≠ 0 := by
  classical
  let pc : (Real × Real) → ℂ := fun x => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I
  let R : Real := 2 * M + 1
  let D := Metric.closedBall y R
  let g : C(D, ℂ) := ⟨fun x => pc (f x) - pc y, by fun_prop⟩
  change (∀ x, g x ≠ 0)
  intro x hx
  apply hmiss x
  have hpc : pc (f x) = pc y := sub_eq_zero.mp hx
  have hpair : f x = y := by
    apply Prod.ext
    · have := congrArg Complex.re hpc
      simpa [pc] using this
    · have := congrArg Complex.im hpc
      simpa [pc] using this
  exact hpair

private noncomputable abbrev T : Set ℝ := by
  classical
  exact Set.Icc (0 : Real) 1

private noncomputable abbrev c (M : ℝ) (y : ℝ × ℝ) : (T) → Real × Real := by
  classical
  let R : Real := 2 * M + 1
  let T := Set.Icc (0 : Real) 1
  change (T → Real × Real)
  exact fun t =>
    (y.1 + R * Real.cos (2 * Real.pi * (t : Real)),
      y.2 + R * Real.sin (2 * Real.pi * (t : Real)))

private theorem hccont (M : ℝ) (y : ℝ × ℝ) : Continuous (c M y) := by
  classical
  let R : Real := 2 * M + 1
  let T := Set.Icc (0 : Real) 1
  let c : T → Real × Real := fun t =>
    (y.1 + R * Real.cos (2 * Real.pi * (t : Real)),
      y.2 + R * Real.sin (2 * Real.pi * (t : Real)))
  change (Continuous c)
  fun_prop

private theorem hcin (M : ℝ) (y : ℝ × ℝ) (hR : 0 ≤ (R M)) : ∀ t, (c M y) t ∈ (D M y) := by
  classical
  let R : Real := 2 * M + 1
  let D := Metric.closedBall y R
  let T := Set.Icc (0 : Real) 1
  let c : T → Real × Real := fun t =>
    (y.1 + R * Real.cos (2 * Real.pi * (t : Real)),
      y.2 + R * Real.sin (2 * Real.pi * (t : Real)))
  change (0 ≤ R) at hR
  change (∀ t, c t ∈ D)
  intro t
  change dist (c t) y ≤ R
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  simp only [c, add_sub_cancel_left]
  apply max_le
  · rw [abs_mul, abs_of_nonneg hR]
    exact mul_le_of_le_one_right hR (Real.abs_cos_le_one _)
  · rw [abs_mul, abs_of_nonneg hR]
    exact mul_le_of_le_one_right hR (Real.abs_sin_le_one _)

private noncomputable abbrev θ : (T) → Real := by
  classical
  let T := Set.Icc (0 : Real) 1
  change (T → Real)
  exact fun t => 2 * Real.pi * (t : Real)

private noncomputable abbrev E : (T) → ℂ := by
  classical
  let T := Set.Icc (0 : Real) 1
  let θ : T → Real := fun t => 2 * Real.pi * (t : Real)
  change (T → ℂ)
  exact fun t => Complex.exp ((θ t : ℂ) * Complex.I)

private theorem hcircle (M : ℝ) (y : ℝ × ℝ) : ∀ t, (pc) ((c M y) t) - (pc) y = ((R M) : ℂ) * (E)
    t := by
  classical
  let pc : (Real × Real) → ℂ := fun x => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I
  let R : Real := 2 * M + 1
  let T := Set.Icc (0 : Real) 1
  let c : T → Real × Real := fun t =>
    (y.1 + R * Real.cos (2 * Real.pi * (t : Real)),
      y.2 + R * Real.sin (2 * Real.pi * (t : Real)))
  let θ : T → Real := fun t => 2 * Real.pi * (t : Real)
  let E : T → ℂ := fun t => Complex.exp ((θ t : ℂ) * Complex.I)
  change (∀ t, pc (c t) - pc y = (R : ℂ) * E t)
  intro t
  apply Complex.ext
  · simp [pc, c, E, θ, Complex.exp_mul_I]
    ring
  · simp [pc, c, E, θ, Complex.exp_mul_I]
    ring

private theorem hE : ∀ t, ‖(E) t‖ = 1 := by
  classical
  let T := Set.Icc (0 : Real) 1
  let θ : T → Real := fun t => 2 * Real.pi * (t : Real)
  let E : T → ℂ := fun t => Complex.exp ((θ t : ℂ) * Complex.I)
  change (∀ t, ‖E t‖ = 1)
  intro t
  simp [E, Complex.norm_exp]

private theorem hEne : ∀ t, (E) t ≠ 0 := by
  classical
  let T := Set.Icc (0 : Real) 1
  let θ : T → Real := fun t => 2 * Real.pi * (t : Real)
  let E : T → ℂ := fun t => Complex.exp ((θ t : ℂ) * Complex.I)
  change (∀ t, E t ≠ 0)
  intro t; exact Complex.exp_ne_zero _

private noncomputable abbrev A (f : ℝ × ℝ → ℝ × ℝ) (M : ℝ) (y : ℝ × ℝ) : (T) → ℂ := by
  classical
  let pc : (Real × Real) → ℂ := fun x => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I
  let R : Real := 2 * M + 1
  let T := Set.Icc (0 : Real) 1
  let c : T → Real × Real := fun t =>
    (y.1 + R * Real.cos (2 * Real.pi * (t : Real)),
      y.2 + R * Real.sin (2 * Real.pi * (t : Real)))
  let θ : T → Real := fun t => 2 * Real.pi * (t : Real)
  let E : T → ℂ := fun t => Complex.exp ((θ t : ℂ) * Complex.I)
  change (T → ℂ)
  exact fun t => (pc (f (c t)) - pc y) / ((R : ℂ) * E t)

private noncomputable abbrev err (f : ℝ × ℝ → ℝ × ℝ) (M : ℝ) (y : ℝ × ℝ) : (T) → ℂ := by
  classical
  let pc : (Real × Real) → ℂ := fun x => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I
  let R : Real := 2 * M + 1
  let T := Set.Icc (0 : Real) 1
  let c : T → Real × Real := fun t =>
    (y.1 + R * Real.cos (2 * Real.pi * (t : Real)),
      y.2 + R * Real.sin (2 * Real.pi * (t : Real)))
  change (T → ℂ)
  exact fun t => pc (f (c t)) - pc (c t)

private theorem hAform (f : ℝ × ℝ → ℝ × ℝ) (M : ℝ) (y : ℝ × ℝ) (hRpos : 0 < (R M)) (hcircle : ∀
    (t : ↑(T)), (pc) ((c M y) t) - (pc) y = ↑(R M) * (E) t) (hEne : ∀ (t : ↑(T)), (E) t ≠ 0) : ∀
    t, (A f M y) t = 1 + (err f M y) t / (((R M) : ℂ) * (E) t) := by
  classical
  let pc : (Real × Real) → ℂ := fun x => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I
  let R : Real := 2 * M + 1
  let T := Set.Icc (0 : Real) 1
  let c : T → Real × Real := fun t =>
    (y.1 + R * Real.cos (2 * Real.pi * (t : Real)),
      y.2 + R * Real.sin (2 * Real.pi * (t : Real)))
  let θ : T → Real := fun t => 2 * Real.pi * (t : Real)
  let E : T → ℂ := fun t => Complex.exp ((θ t : ℂ) * Complex.I)
  let A : T → ℂ := fun t => (pc (f (c t)) - pc y) / ((R : ℂ) * E t)
  let err : T → ℂ := fun t => pc (f (c t)) - pc (c t)
  change (0 < R) at hRpos
  change (∀ (t : ↑T), pc (c t) - pc y = ↑R * E t) at hcircle
  change (∀ (t : ↑T), E t ≠ 0) at hEne
  change (∀ t, A t = 1 + err t / ((R : ℂ) * E t))
  intro t
  have hden : (R : ℂ) * E t ≠ 0 := mul_ne_zero (by exact_mod_cast hRpos.ne') (hEne t)
  have hsum : pc (f (c t)) - pc y = err t + (R : ℂ) * E t := by
    dsimp [err]
    rw [← hcircle t]
    ring
  dsimp [A]
  rw [hsum]
  field_simp [hden, hRpos.ne', hEne t]
  ring

private theorem hcoord (f : ℝ × ℝ → ℝ × ℝ) (M : ℝ) (hbound : ∀ (x : ℝ × ℝ), dist (f x) x ≤ M) (y
    : ℝ × ℝ) : ∀ t, |(f ((c M y) t)).1 - ((c M y) t).1| ≤ M ∧
      |(f ((c M y) t)).2 - ((c M y) t).2| ≤ M := by
  classical
  let R : Real := 2 * M + 1
  let T := Set.Icc (0 : Real) 1
  let c : T → Real × Real := fun t =>
    (y.1 + R * Real.cos (2 * Real.pi * (t : Real)),
      y.2 + R * Real.sin (2 * Real.pi * (t : Real)))
  change (∀ t, |(f (c t)).1 - (c t).1| ≤ M ∧
      |(f (c t)).2 - (c t).2| ≤ M)
  intro t
  have h := hbound (c t)
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq] at h
  exact ⟨(le_max_left _ _).trans h, (le_max_right _ _).trans h⟩

private theorem herr (f : ℝ × ℝ → ℝ × ℝ) (M : ℝ) (y : ℝ × ℝ) (hcoord : ∀ (t : ↑(T)), |(f ((c M y)
    t)).1 - ((c M y) t).1| ≤ M ∧ |(f ((c M y) t)).2 - ((c M y) t).2| ≤ M) : ∀ t, ‖(err f M y) t‖
    ≤ 2 * M := by
  classical
  let pc : (Real × Real) → ℂ := fun x => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I
  let R : Real := 2 * M + 1
  let T := Set.Icc (0 : Real) 1
  let c : T → Real × Real := fun t =>
    (y.1 + R * Real.cos (2 * Real.pi * (t : Real)),
      y.2 + R * Real.sin (2 * Real.pi * (t : Real)))
  let err : T → ℂ := fun t => pc (f (c t)) - pc (c t)
  change (∀ (t : ↑T), |(f (c t)).1 - (c t).1| ≤ M ∧ |(f (c t)).2 - (c t).2| ≤ M) at hcoord
  change (∀ t, ‖err t‖ ≤ 2 * M)
  intro t
  have hc := hcoord t
  have heq : err t = (((f (c t)).1 - (c t).1 : Real) : ℂ) +
      (((f (c t)).2 - (c t).2 : Real) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [err, pc]
  rw [heq]
  calc
    ‖(((f (c t)).1 - (c t).1 : Real) : ℂ) +
        (((f (c t)).2 - (c t).2 : Real) : ℂ) * Complex.I‖ ≤
        ‖(((f (c t)).1 - (c t).1 : Real) : ℂ)‖ +
        ‖(((f (c t)).2 - (c t).2 : Real) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |(f (c t)).1 - (c t).1| + |(f (c t)).2 - (c t).2| := by
      have hfirst : ‖(((f (c t)).1 - (c t).1 : Real) : ℂ)‖ =
          |(f (c t)).1 - (c t).1| := by
        simp only [Complex.norm_real, Real.norm_eq_abs]
      have hsecond : ‖(((f (c t)).2 - (c t).2 : Real) : ℂ) * Complex.I‖ =
          |(f (c t)).2 - (c t).2| := by
        simp only [Complex.norm_mul, Complex.norm_real,
          Complex.norm_I, mul_one, Real.norm_eq_abs]
      rw [hfirst, hsecond]
    _ ≤ 2 * M := by linarith [hc.1, hc.2]

private theorem hAclose (f : ℝ × ℝ → ℝ × ℝ) (M : ℝ) (hM : 0 ≤ M) (y : ℝ × ℝ) (hR : 0 ≤ (R M))
    (hMR : 2 * M < (R M)) (hE : ∀ (t : ↑(T)), ‖(E) t‖ = 1) (hAform : ∀ (t : ↑(T)), (A f M y) t =
    1 + (err f M y) t / (↑(R M) * (E) t)) (herr : ∀ (t : ↑(T)), ‖(err f M y) t‖ ≤ 2 * M) : ∀ t,
    ‖(A f M y) t - 1‖ < 1 := by
  classical
  let pc : (Real × Real) → ℂ := fun x => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I
  let R : Real := 2 * M + 1
  let T := Set.Icc (0 : Real) 1
  let c : T → Real × Real := fun t =>
    (y.1 + R * Real.cos (2 * Real.pi * (t : Real)),
      y.2 + R * Real.sin (2 * Real.pi * (t : Real)))
  let θ : T → Real := fun t => 2 * Real.pi * (t : Real)
  let E : T → ℂ := fun t => Complex.exp ((θ t : ℂ) * Complex.I)
  let A : T → ℂ := fun t => (pc (f (c t)) - pc y) / ((R : ℂ) * E t)
  let err : T → ℂ := fun t => pc (f (c t)) - pc (c t)
  change (0 ≤ R) at hR
  change (2 * M < R) at hMR
  change (∀ (t : ↑T), ‖E t‖ = 1) at hE
  change (∀ (t : ↑T), A t = 1 + err t / (↑R * E t)) at hAform
  change (∀ (t : ↑T), ‖err t‖ ≤ 2 * M) at herr
  change (∀ t, ‖A t - 1‖ < 1)
  intro t
  rw [hAform t, add_sub_cancel_left]
  have hden : ‖(R : ℂ) * E t‖ = R := by simp [hE t, hR]
  rw [norm_div, hden]
  exact (div_lt_one (by positivity)).2 ((herr t).trans_lt hMR)

private theorem hreA (f : ℝ × ℝ → ℝ × ℝ) (M : ℝ) (y : ℝ × ℝ) (hAclose : ∀ (t : ↑(T)), ‖(A f M y)
    t - 1‖ < 1) : ∀ t, 0 < ((A f M y) t).re := by
  classical
  let pc : (Real × Real) → ℂ := fun x => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I
  let R : Real := 2 * M + 1
  let T := Set.Icc (0 : Real) 1
  let c : T → Real × Real := fun t =>
    (y.1 + R * Real.cos (2 * Real.pi * (t : Real)),
      y.2 + R * Real.sin (2 * Real.pi * (t : Real)))
  let θ : T → Real := fun t => 2 * Real.pi * (t : Real)
  let E : T → ℂ := fun t => Complex.exp ((θ t : ℂ) * Complex.I)
  let A : T → ℂ := fun t => (pc (f (c t)) - pc y) / ((R : ℂ) * E t)
  change (∀ (t : ↑T), ‖A t - 1‖ < 1) at hAclose
  change (∀ t, 0 < (A t).re)
  intro t
  have hn := hAclose t
  have hreal : |(A t).re - 1| ≤ ‖A t - 1‖ := by
    simpa using Complex.abs_re_le_norm (A t - 1)
  have : |(A t).re - 1| < 1 := lt_of_le_of_lt hreal hn
  rw [abs_lt] at this
  linarith

private theorem hAcont (f : ℝ × ℝ → ℝ × ℝ) (hf : Continuous f) (M : ℝ) (y : ℝ × ℝ) (hRpos : 0 <
    (R M)) (hccont : Continuous (c M y)) (hEne : ∀ (t : ↑(T)), (E) t ≠ 0) : Continuous (A f M y)
    := by
  classical
  let pc : (Real × Real) → ℂ := fun x => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I
  let R : Real := 2 * M + 1
  let T := Set.Icc (0 : Real) 1
  let c : T → Real × Real := fun t =>
    (y.1 + R * Real.cos (2 * Real.pi * (t : Real)),
      y.2 + R * Real.sin (2 * Real.pi * (t : Real)))
  let θ : T → Real := fun t => 2 * Real.pi * (t : Real)
  let E : T → ℂ := fun t => Complex.exp ((θ t : ℂ) * Complex.I)
  let A : T → ℂ := fun t => (pc (f (c t)) - pc y) / ((R : ℂ) * E t)
  change (0 < R) at hRpos
  change (Continuous c) at hccont
  change (∀ (t : ↑T), E t ≠ 0) at hEne
  change (Continuous A)
  have hdencont : Continuous (fun t : T => (R : ℂ) * E t) := by fun_prop
  have hdenne : ∀ t : T, (R : ℂ) * E t ≠ 0 := by
    intro t
    exact mul_ne_zero (by exact_mod_cast hRpos.ne') (hEne t)
  have hnumcont : Continuous (fun t : T => pc (f (c t)) - pc y) := by fun_prop
  exact hnumcont.div hdencont hdenne

private theorem hlogcont (f : ℝ × ℝ → ℝ × ℝ) (M : ℝ) (y : ℝ × ℝ) (hreA : ∀ (t : ↑(T)), 0 < ((A f
    M y) t).re) (hAcont : Continuous (A f M y)) : Continuous (fun t : (T) => Complex.log ((A f M
    y) t)) := by
  classical
  let pc : (Real × Real) → ℂ := fun x => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I
  let R : Real := 2 * M + 1
  let T := Set.Icc (0 : Real) 1
  let c : T → Real × Real := fun t =>
    (y.1 + R * Real.cos (2 * Real.pi * (t : Real)),
      y.2 + R * Real.sin (2 * Real.pi * (t : Real)))
  let θ : T → Real := fun t => 2 * Real.pi * (t : Real)
  let E : T → ℂ := fun t => Complex.exp ((θ t : ℂ) * Complex.I)
  let A : T → ℂ := fun t => (pc (f (c t)) - pc y) / ((R : ℂ) * E t)
  change (∀ (t : ↑T), 0 < (A t).re) at hreA
  change (Continuous A) at hAcont
  change (Continuous (fun t : T => Complex.log (A t)))
  apply hAcont.clog
  intro t
  rw [Complex.mem_slitPlane_iff]
  exact Or.inl (hreA t)

private theorem hexpL (f : ℝ × ℝ → ℝ × ℝ) (M : ℝ) (y : ℝ × ℝ) (hreA : ∀ (t : ↑(T)), 0 < ((A f M
    y) t).re) : ∀ t, Complex.exp (Complex.log ((A f M y) t)) = (A f M y) t := by
  classical
  let pc : (Real × Real) → ℂ := fun x => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I
  let R : Real := 2 * M + 1
  let T := Set.Icc (0 : Real) 1
  let c : T → Real × Real := fun t =>
    (y.1 + R * Real.cos (2 * Real.pi * (t : Real)),
      y.2 + R * Real.sin (2 * Real.pi * (t : Real)))
  let θ : T → Real := fun t => 2 * Real.pi * (t : Real)
  let E : T → ℂ := fun t => Complex.exp ((θ t : ℂ) * Complex.I)
  let A : T → ℂ := fun t => (pc (f (c t)) - pc y) / ((R : ℂ) * E t)
  change (∀ (t : ↑T), 0 < (A t).re) at hreA
  change (∀ t, Complex.exp (Complex.log (A t)) = A t)
  intro t
  apply Complex.exp_log
  intro hz
  have : (A t).re = 0 := by rw [hz]; simp
  linarith [hreA t]

private noncomputable abbrev J (f : ℝ × ℝ → ℝ × ℝ) (M : ℝ) (y : ℝ × ℝ) (F : C(↑(Metric.closedBall
    y (R M)), ℂ)) (hcin : ∀ (t : ↑(T)), (c M y) t ∈ (D M y)) : (T) → ℂ := by
  classical
  let pc : (Real × Real) → ℂ := fun x => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I
  let R : Real := 2 * M + 1
  let D := Metric.closedBall y R
  let T := Set.Icc (0 : Real) 1
  let c : T → Real × Real := fun t =>
    (y.1 + R * Real.cos (2 * Real.pi * (t : Real)),
      y.2 + R * Real.sin (2 * Real.pi * (t : Real)))
  let θ : T → Real := fun t => 2 * Real.pi * (t : Real)
  let E : T → ℂ := fun t => Complex.exp ((θ t : ℂ) * Complex.I)
  let A : T → ℂ := fun t => (pc (f (c t)) - pc y) / ((R : ℂ) * E t)
  change (C(↑(Metric.closedBall y R), ℂ)) at F
  change (∀ (t : ↑T), c t ∈ D) at hcin
  change (T → ℂ)
  exact fun t => F ⟨c t, hcin t⟩ -
    (Real.log R + (θ t : ℂ) * Complex.I + Complex.log (A t))

private theorem hJcont (f : ℝ × ℝ → ℝ × ℝ) (M : ℝ) (y : ℝ × ℝ) (F : C(↑(Metric.closedBall y (R
    M)), ℂ)) (hccont : Continuous (c M y)) (hcin : ∀ (t : ↑(T)), (c M y) t ∈ (D M y)) (hlogcont :
    Continuous fun t => Complex.log ((A f M y) t)) : Continuous (J f M y F hcin) := by
  classical
  let pc : (Real × Real) → ℂ := fun x => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I
  let R : Real := 2 * M + 1
  let D := Metric.closedBall y R
  let T := Set.Icc (0 : Real) 1
  let c : T → Real × Real := fun t =>
    (y.1 + R * Real.cos (2 * Real.pi * (t : Real)),
      y.2 + R * Real.sin (2 * Real.pi * (t : Real)))
  let θ : T → Real := fun t => 2 * Real.pi * (t : Real)
  let E : T → ℂ := fun t => Complex.exp ((θ t : ℂ) * Complex.I)
  let A : T → ℂ := fun t => (pc (f (c t)) - pc y) / ((R : ℂ) * E t)
  let J : T → ℂ := fun t => F ⟨c t, hcin t⟩ -
    (Real.log R + (θ t : ℂ) * Complex.I + Complex.log (A t))
  change (C(↑(Metric.closedBall y R), ℂ)) at F
  change (Continuous c) at hccont
  change (∀ (t : ↑T), c t ∈ D) at hcin
  change (Continuous fun t => Complex.log (A t)) at hlogcont
  change (Continuous J)
  dsimp [J]
  fun_prop

private theorem hJexp (f : ℝ × ℝ → ℝ × ℝ) (hf : Continuous f) (M : ℝ) (y : ℝ × ℝ) (hmiss : ∀ (x :
    ℝ × ℝ), f x ≠ y) (hRpos : 0 < (R M)) (F : C(↑(Metric.closedBall y (R M)), ℂ)) (hF : ∀ (x :
    ↑(Metric.closedBall y (R M))), Complex.exp (F x) = (g f hf M y) x) (hcin : ∀ (t : ↑(T)), (c M
    y) t ∈ (D M y)) (hEne : ∀ (t : ↑(T)), (E) t ≠ 0) (hAform : ∀ (t : ↑(T)), (A f M y) t = 1 +
    (err f M y) t / (↑(R M) * (E) t)) (hexpL : ∀ (t : ↑(T)), Complex.exp (Complex.log ((A f M y)
    t)) = (A f M y) t) : ∀ t, Complex.exp ((J f M y F hcin) t) = 1 := by
  classical
  let pc : (Real × Real) → ℂ := fun x => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I
  let R : Real := 2 * M + 1
  let D := Metric.closedBall y R
  let g : C(D, ℂ) := ⟨fun x => pc (f x) - pc y, by fun_prop⟩
  let T := Set.Icc (0 : Real) 1
  let c : T → Real × Real := fun t =>
    (y.1 + R * Real.cos (2 * Real.pi * (t : Real)),
      y.2 + R * Real.sin (2 * Real.pi * (t : Real)))
  let θ : T → Real := fun t => 2 * Real.pi * (t : Real)
  let E : T → ℂ := fun t => Complex.exp ((θ t : ℂ) * Complex.I)
  let A : T → ℂ := fun t => (pc (f (c t)) - pc y) / ((R : ℂ) * E t)
  let err : T → ℂ := fun t => pc (f (c t)) - pc (c t)
  let J : T → ℂ := fun t => F ⟨c t, hcin t⟩ -
    (Real.log R + (θ t : ℂ) * Complex.I + Complex.log (A t))
  change (0 < R) at hRpos
  change (C(↑(Metric.closedBall y R), ℂ)) at F
  change (∀ (x : ↑(Metric.closedBall y R)), Complex.exp (F x) = g x) at hF
  change (∀ (t : ↑T), c t ∈ D) at hcin
  change (∀ (t : ↑T), E t ≠ 0) at hEne
  change (∀ (t : ↑T), A t = 1 + err t / (↑R * E t)) at hAform
  change (∀ (t : ↑T), Complex.exp (Complex.log (A t)) = A t) at hexpL
  change (∀ t, Complex.exp (J t) = 1)
  intro t
  have hFval := hF ⟨c t, hcin t⟩
  have hfac : (R : ℂ) * E t * A t = pc (f (c t)) - pc y := by
    dsimp [A]
    have hden : (R : ℂ) * E t ≠ 0 := mul_ne_zero (by exact_mod_cast hRpos.ne') (hEne t)
    field_simp [hden, hRpos.ne', hEne t]
  have hfac' : (R : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I) * A t =
      pc (f (c t)) - pc y := by simpa [E] using hfac
  have hsum : Complex.exp (Real.log R + (θ t : ℂ) * Complex.I +
      Complex.log (A t)) = pc (f (c t)) - pc y := by
    rw [Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hRpos,
      hexpL t]
    convert hfac' using 1
  rw [Complex.exp_sub, hFval, hsum]
  exact div_self (sub_ne_zero.mpr (by
    intro hz
    apply hmiss (c t)
    have hp : pc (f (c t)) = pc y := hz
    apply Prod.ext
    · have := congrArg Complex.re hp; simpa [pc] using this
    · have := congrArg Complex.im hp; simpa [pc] using this))

private theorem hJzero (f : ℝ × ℝ → ℝ × ℝ) (M : ℝ) (y : ℝ × ℝ) (F : C(↑(Metric.closedBall y (R
    M)), ℂ)) (hcin : ∀ (t : ↑(T)), (c M y) t ∈ (D M y)) (hJexp : ∀ (t : ↑(T)), Complex.exp ((J f
    M y F hcin) t) = 1) : ∀ t, ∃ n : Int, ((J f M y F hcin) t).im / (2 * Real.pi) = n := by
  classical
  let pc : (Real × Real) → ℂ := fun x => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I
  let R : Real := 2 * M + 1
  let D := Metric.closedBall y R
  let T := Set.Icc (0 : Real) 1
  let c : T → Real × Real := fun t =>
    (y.1 + R * Real.cos (2 * Real.pi * (t : Real)),
      y.2 + R * Real.sin (2 * Real.pi * (t : Real)))
  let θ : T → Real := fun t => 2 * Real.pi * (t : Real)
  let E : T → ℂ := fun t => Complex.exp ((θ t : ℂ) * Complex.I)
  let A : T → ℂ := fun t => (pc (f (c t)) - pc y) / ((R : ℂ) * E t)
  let J : T → ℂ := fun t => F ⟨c t, hcin t⟩ -
    (Real.log R + (θ t : ℂ) * Complex.I + Complex.log (A t))
  change (C(↑(Metric.closedBall y R), ℂ)) at F
  change (∀ (t : ↑T), c t ∈ D) at hcin
  change (∀ (t : ↑T), Complex.exp (J t) = 1) at hJexp
  change (∀ t, ∃ n : Int, (J t).im / (2 * Real.pi) = n)
  intro t
  obtain ⟨n, hn⟩ := (Complex.exp_eq_one_iff).mp (hJexp t)
  refine ⟨n, ?_⟩
  rw [hn]
  simp [Complex.mul_re, Complex.mul_im]

private theorem hJcontIm (f : ℝ × ℝ → ℝ × ℝ) (M : ℝ) (y : ℝ × ℝ) (F : C(↑(Metric.closedBall y (R
    M)), ℂ)) (hcin : ∀ (t : ↑(T)), (c M y) t ∈ (D M y)) (hJcont : Continuous (J f M y F hcin)) :
    Continuous (fun t : (T) => ((J f M y F hcin) t).im / (2 * Real.pi)) := by
  classical
  let pc : (Real × Real) → ℂ := fun x => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I
  let R : Real := 2 * M + 1
  let D := Metric.closedBall y R
  let T := Set.Icc (0 : Real) 1
  let c : T → Real × Real := fun t =>
    (y.1 + R * Real.cos (2 * Real.pi * (t : Real)),
      y.2 + R * Real.sin (2 * Real.pi * (t : Real)))
  let θ : T → Real := fun t => 2 * Real.pi * (t : Real)
  let E : T → ℂ := fun t => Complex.exp ((θ t : ℂ) * Complex.I)
  let A : T → ℂ := fun t => (pc (f (c t)) - pc y) / ((R : ℂ) * E t)
  let J : T → ℂ := fun t => F ⟨c t, hcin t⟩ -
    (Real.log R + (θ t : ℂ) * Complex.I + Complex.log (A t))
  change (C(↑(Metric.closedBall y R), ℂ)) at F
  change (∀ (t : ↑T), c t ∈ D) at hcin
  change (Continuous J) at hJcont
  change (Continuous (fun t : T => (J t).im / (2 * Real.pi)))
  exact (Complex.continuous_im.comp hJcont).div_const _

private noncomputable abbrev t0 : (T) := by
  classical
  let T := Set.Icc (0 : Real) 1
  change (T)
  exact ⟨0, by norm_num [T]⟩

private noncomputable abbrev t1 : (T) := by
  classical
  let T := Set.Icc (0 : Real) 1
  change (T)
  exact ⟨1, by norm_num [T]⟩

private theorem hJend (f : ℝ × ℝ → ℝ × ℝ) (M : ℝ) (y : ℝ × ℝ) (F : C(↑(Metric.closedBall y (R
    M)), ℂ)) (hcin : ∀ (t : ↑(T)), (c M y) t ∈ (D M y)) (hJexp : ∀ (t : ↑(T)), Complex.exp ((J f
    M y F hcin) t) = 1) (hJzero : ∀ (t : ↑(T)), ∃ n : Int, ((J f M y F hcin) t).im / (2 *
    Real.pi) = ↑n) (hJcontIm : Continuous fun t => ((J f M y F hcin) t).im / (2 * Real.pi)) : (J
    f M y F hcin) (t0) = (J f M y F hcin) (t1) := by
  classical
  let pc : (Real × Real) → ℂ := fun x => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I
  let R : Real := 2 * M + 1
  let D := Metric.closedBall y R
  let T := Set.Icc (0 : Real) 1
  let c : T → Real × Real := fun t =>
    (y.1 + R * Real.cos (2 * Real.pi * (t : Real)),
      y.2 + R * Real.sin (2 * Real.pi * (t : Real)))
  let θ : T → Real := fun t => 2 * Real.pi * (t : Real)
  let E : T → ℂ := fun t => Complex.exp ((θ t : ℂ) * Complex.I)
  let A : T → ℂ := fun t => (pc (f (c t)) - pc y) / ((R : ℂ) * E t)
  let J : T → ℂ := fun t => F ⟨c t, hcin t⟩ -
    (Real.log R + (θ t : ℂ) * Complex.I + Complex.log (A t))
  let t0 : T := ⟨0, by norm_num [T]⟩
  let t1 : T := ⟨1, by norm_num [T]⟩
  change (C(↑(Metric.closedBall y R), ℂ)) at F
  change (∀ (t : ↑T), c t ∈ D) at hcin
  change (∀ (t : ↑T), Complex.exp (J t) = 1) at hJexp
  change (∀ (t : ↑T), ∃ n : Int, (J t).im / (2 * Real.pi) = ↑n) at hJzero
  change (Continuous fun t => (J t).im / (2 * Real.pi)) at hJcontIm
  change (J t0 = J t1)
  have hfiber : ∀ t : T, ∃ n : Int, J t = (n : ℂ) * (2 * Real.pi * Complex.I) := by
    intro t
    obtain ⟨n, hn⟩ := (Complex.exp_eq_one_iff).mp (hJexp t)
    exact ⟨n, hn⟩
  obtain ⟨n0, hn0⟩ := hfiber t0
  obtain ⟨n1, hn1⟩ := hfiber t1
  have him0 : (J t0).im / (2 * Real.pi) = (n0 : ℝ) := by rw [hn0]; simp
  have him1 : (J t1).im / (2 * Real.pi) = (n1 : ℝ) := by rw [hn1]; simp
  by_contra hneq
  have hnneq : n0 ≠ n1 := by
    intro heq
    apply hneq
    rw [hn0, hn1, heq]
  rcases lt_or_gt_of_ne hnneq with hlt | hgt
  · have hgap : n0 + 1 ≤ n1 := Int.add_one_le_iff.mpr hlt
    have hgapR : (n0 : ℝ) + 1 ≤ (n1 : ℝ) := by exact_mod_cast hgap
    let q : ℝ := (n0 : ℝ) + 1 / 2
    have hqlo : (J t0).im / (2 * Real.pi) ≤ q := by rw [him0]; dsimp [q]; linarith
    have hqhi : q ≤ (J t1).im / (2 * Real.pi) := by rw [him1]; dsimp [q]; linarith
    have hrange := intermediate_value_Icc (show t0 ≤ t1 by norm_num [t0, t1, T])
      hJcontIm.continuousOn (Set.mem_Icc.mpr ⟨hqlo, hqhi⟩)
    rcases hrange with ⟨t, ht, hqt⟩
    obtain ⟨n, hn⟩ := hJzero t
    have : (n0 : ℝ) + 1 / 2 = (n : ℝ) := by
      have hqt' : (J t).im / (2 * Real.pi) = q := by simpa using hqt
      rw [hn] at hqt'
      dsimp [q] at hqt'
      exact hqt'.symm
    have hcastR : (2 : ℝ) * (n0 : ℝ) + 1 = 2 * (n : ℝ) := by nlinarith [this]
    have hcast : (2 * n0 + 1 : Int) = 2 * n := by exact_mod_cast hcastR
    omega
  · have hgap : n1 + 1 ≤ n0 := Int.add_one_le_iff.mpr hgt
    have hgapR : (n1 : ℝ) + 1 ≤ (n0 : ℝ) := by exact_mod_cast hgap
    let q : ℝ := (n1 : ℝ) + 1 / 2
    have hqlo : -((J t0).im / (2 * Real.pi)) ≤ -q := by rw [him0]; dsimp [q]; linarith
    have hqhi : -q ≤ -((J t1).im / (2 * Real.pi)) := by rw [him1]; dsimp [q]; linarith
    have hrange := intermediate_value_Icc (show t0 ≤ t1 by norm_num [t0, t1, T])
      hJcontIm.neg.continuousOn (Set.mem_Icc.mpr ⟨hqlo, hqhi⟩)
    rcases hrange with ⟨t, ht, hqt⟩
    obtain ⟨n, hn⟩ := hJzero t
    have : (n1 : ℝ) + 1 / 2 = (n : ℝ) := by
      change -((J t).im / (2 * Real.pi)) = -q at hqt
      have hqt' : (J t).im / (2 * Real.pi) = q := by linarith
      rw [hn] at hqt'
      dsimp [q] at hqt'
      exact hqt'.symm
    have hcastR : (2 : ℝ) * (n1 : ℝ) + 1 = 2 * (n : ℝ) := by nlinarith [this]
    have hcast : (2 * n1 + 1 : Int) = 2 * n := by exact_mod_cast hcastR
    omega

private theorem hcircleend (M : ℝ) (y : ℝ × ℝ) : (c M y) (t0) = (c M y) (t1) := by
  classical
  let R : Real := 2 * M + 1
  let T := Set.Icc (0 : Real) 1
  let c : T → Real × Real := fun t =>
    (y.1 + R * Real.cos (2 * Real.pi * (t : Real)),
      y.2 + R * Real.sin (2 * Real.pi * (t : Real)))
  let t0 : T := ⟨0, by norm_num [T]⟩
  let t1 : T := ⟨1, by norm_num [T]⟩
  change (c t0 = c t1)
  simp [c, t0, t1, T, Real.cos_two_pi, Real.sin_two_pi]

private theorem hEend : (E) (t0) = (E) (t1) := by
  classical
  let T := Set.Icc (0 : Real) 1
  let θ : T → Real := fun t => 2 * Real.pi * (t : Real)
  let E : T → ℂ := fun t => Complex.exp ((θ t : ℂ) * Complex.I)
  let t0 : T := ⟨0, by norm_num [T]⟩
  let t1 : T := ⟨1, by norm_num [T]⟩
  change (E t0 = E t1)
  simp [E, θ, t0, t1, T, Complex.exp_mul_I]

private theorem hAend (f : ℝ × ℝ → ℝ × ℝ) (M : ℝ) (y : ℝ × ℝ) (hcircleend : (c M y) (t0) = (c M
    y) (t1)) (hEend : (E) (t0) = (E) (t1)) : (A f M y) (t0) = (A f M y) (t1) := by
  classical
  let pc : (Real × Real) → ℂ := fun x => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I
  let R : Real := 2 * M + 1
  let T := Set.Icc (0 : Real) 1
  let c : T → Real × Real := fun t =>
    (y.1 + R * Real.cos (2 * Real.pi * (t : Real)),
      y.2 + R * Real.sin (2 * Real.pi * (t : Real)))
  let θ : T → Real := fun t => 2 * Real.pi * (t : Real)
  let E : T → ℂ := fun t => Complex.exp ((θ t : ℂ) * Complex.I)
  let A : T → ℂ := fun t => (pc (f (c t)) - pc y) / ((R : ℂ) * E t)
  let t0 : T := ⟨0, by norm_num [T]⟩
  let t1 : T := ⟨1, by norm_num [T]⟩
  change (c t0 = c t1) at hcircleend
  change (E t0 = E t1) at hEend
  change (A t0 = A t1)
  change (pc (f (c t0)) - pc y) / ((R : ℂ) * E t0) =
    (pc (f (c t1)) - pc y) / ((R : ℂ) * E t1)
  rw [hcircleend, hEend]

private theorem hJdiff (f : ℝ × ℝ → ℝ × ℝ) (M : ℝ) (y : ℝ × ℝ) (F : C(↑(Metric.closedBall y (R
    M)), ℂ)) (hcin : ∀ (t : ↑(T)), (c M y) t ∈ (D M y)) (hcircleend : (c M y) (t0) = (c M y)
    (t1)) (hAend : (A f M y) (t0) = (A f M y) (t1)) : (J f M y F hcin) (t1) - (J f M y F hcin)
    (t0) =
      -(2 * Real.pi * Complex.I) := by
  classical
  let pc : (Real × Real) → ℂ := fun x => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I
  let R : Real := 2 * M + 1
  let D := Metric.closedBall y R
  let T := Set.Icc (0 : Real) 1
  let c : T → Real × Real := fun t =>
    (y.1 + R * Real.cos (2 * Real.pi * (t : Real)),
      y.2 + R * Real.sin (2 * Real.pi * (t : Real)))
  let θ : T → Real := fun t => 2 * Real.pi * (t : Real)
  let E : T → ℂ := fun t => Complex.exp ((θ t : ℂ) * Complex.I)
  let A : T → ℂ := fun t => (pc (f (c t)) - pc y) / ((R : ℂ) * E t)
  let J : T → ℂ := fun t => F ⟨c t, hcin t⟩ -
    (Real.log R + (θ t : ℂ) * Complex.I + Complex.log (A t))
  let t0 : T := ⟨0, by norm_num [T]⟩
  let t1 : T := ⟨1, by norm_num [T]⟩
  change (C(↑(Metric.closedBall y R), ℂ)) at F
  change (∀ (t : ↑T), c t ∈ D) at hcin
  change (c t0 = c t1) at hcircleend
  change (A t0 = A t1) at hAend
  change (J t1 - J t0 =
      -(2 * Real.pi * Complex.I))
  have hFend : F ⟨c t0, hcin t0⟩ = F ⟨c t1, hcin t1⟩ := by
    congr 1
    exact Subtype.ext hcircleend
  have ht0 : θ t0 = 0 := by simp [θ, t0, T]
  have ht1 : θ t1 = 2 * Real.pi := by simp [θ, t1, T]
  dsimp [J]
  rw [hFend, hAend, ht0, ht1]
  push_cast
  ring

private theorem hpi : (2 * Real.pi : ℂ) ≠ 0 := by
  classical
  exact_mod_cast (mul_ne_zero (by norm_num) Real.pi_ne_zero)

private theorem hI : Complex.I ≠ 0 := by
  classical
  exact Complex.I_ne_zero

end BoundedDisplacementConstruction

theorem P3776T1BoundedDisplacementSurjective
    (f : (Real × Real) → (Real × Real)) (hf : Continuous f)
    (hbound : ∃ M : Real, 0 ≤ M ∧ ∀ x, dist (f x) x ≤ M) :
    Function.Surjective f := by
-- BODY
  obtain ⟨M, hM, hbound⟩ := hbound
  intro y
  by_contra hnot
  have hmiss : ∀ x, f x ≠ y := BoundedDisplacementConstruction.hmiss f y hnot
  let pc : (Real × Real) → ℂ := fun x => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I
  let R : Real := 2 * M + 1
  have hR : 0 ≤ R := BoundedDisplacementConstruction.hR M hM
  have hRpos : 0 < R := BoundedDisplacementConstruction.hRpos M hM
  have hMR : 2 * M < R := BoundedDisplacementConstruction.hMR M
  let D := Metric.closedBall y R
  let g : C(D, ℂ) := ⟨fun x => pc (f x) - pc y, by fun_prop⟩
  have hg : ∀ x, g x ≠ 0 := BoundedDisplacementConstruction.hg f hf M y hmiss
  obtain ⟨F, hF⟩ := P3776T1DiskMapExponentialLift y R hR g hg
  let T := Set.Icc (0 : Real) 1
  let c : T → Real × Real := fun t =>
    (y.1 + R * Real.cos (2 * Real.pi * (t : Real)),
      y.2 + R * Real.sin (2 * Real.pi * (t : Real)))
  have hccont : Continuous c := BoundedDisplacementConstruction.hccont M y
  have hcin : ∀ t, c t ∈ D := BoundedDisplacementConstruction.hcin M y hR
  let θ : T → Real := fun t => 2 * Real.pi * (t : Real)
  let E : T → ℂ := fun t => Complex.exp ((θ t : ℂ) * Complex.I)
  have hcircle : ∀ t, pc (c t) - pc y = (R : ℂ) * E t := BoundedDisplacementConstruction.hcircle M y
  have hE : ∀ t, ‖E t‖ = 1 := BoundedDisplacementConstruction.hE
  have hEne : ∀ t, E t ≠ 0 := BoundedDisplacementConstruction.hEne
  let A : T → ℂ := fun t => (pc (f (c t)) - pc y) / ((R : ℂ) * E t)
  let err : T → ℂ := fun t => pc (f (c t)) - pc (c t)
  have hAform : ∀ t, A t = 1 + err t / ((R : ℂ) * E t) := BoundedDisplacementConstruction.hAform
      f M y hRpos hcircle hEne
  have hcoord : ∀ t, |(f (c t)).1 - (c t).1| ≤ M ∧
      |(f (c t)).2 - (c t).2| ≤ M := BoundedDisplacementConstruction.hcoord f M hbound y
  have herr : ∀ t, ‖err t‖ ≤ 2 * M := BoundedDisplacementConstruction.herr f M y hcoord
  have hAclose : ∀ t, ‖A t - 1‖ < 1 := BoundedDisplacementConstruction.hAclose f M hM y hR hMR hE
      hAform herr
  have hreA : ∀ t, 0 < (A t).re := BoundedDisplacementConstruction.hreA f M y hAclose
  have hAcont : Continuous A := BoundedDisplacementConstruction.hAcont f hf M y hRpos hccont hEne
  have hlogcont : Continuous (fun t : T => Complex.log (A t)) :=
      BoundedDisplacementConstruction.hlogcont f M y hreA hAcont
  have hexpL : ∀ t, Complex.exp (Complex.log (A t)) = A t :=
      BoundedDisplacementConstruction.hexpL f M y hreA
  let J : T → ℂ := fun t => F ⟨c t, hcin t⟩ -
    (Real.log R + (θ t : ℂ) * Complex.I + Complex.log (A t))
  have hJcont : Continuous J := BoundedDisplacementConstruction.hJcont f M y F hccont hcin hlogcont
  have hJexp : ∀ t, Complex.exp (J t) = 1 := BoundedDisplacementConstruction.hJexp f hf M y hmiss
      hRpos F hF hcin hEne hAform hexpL
  have hJzero : ∀ t, ∃ n : Int, (J t).im / (2 * Real.pi) = n :=
      BoundedDisplacementConstruction.hJzero f M y F hcin hJexp
  have hJcontIm : Continuous (fun t : T => (J t).im / (2 * Real.pi)) :=
      BoundedDisplacementConstruction.hJcontIm f M y F hcin hJcont
  let t0 : T := ⟨0, by norm_num [T]⟩
  let t1 : T := ⟨1, by norm_num [T]⟩
  have hJend : J t0 = J t1 := BoundedDisplacementConstruction.hJend f M y F hcin hJexp hJzero
      hJcontIm
  have hcircleend : c t0 = c t1 := BoundedDisplacementConstruction.hcircleend M y
  have hEend : E t0 = E t1 := BoundedDisplacementConstruction.hEend
  have hAend : A t0 = A t1 := BoundedDisplacementConstruction.hAend f M y hcircleend hEend
  have hJdiff : J t1 - J t0 =
      -(2 * Real.pi * Complex.I) := BoundedDisplacementConstruction.hJdiff f M y F hcin
          hcircleend hAend
  have : J t0 = J t1 := hJend
  rw [this] at hJdiff
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := BoundedDisplacementConstruction.hpi
  have hI : Complex.I ≠ 0 := BoundedDisplacementConstruction.hI
  have : (2 * Real.pi : ℂ) * Complex.I ≠ 0 := mul_ne_zero hpi hI
  exact (this (by linear_combination hJdiff))

end ApollonianSuperharmonic

end
