/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Basic.Domains
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
Periodicity on the complex cover and the real torus with period 2 * pi. Periodicity constrains
values on the specified phase domain; arbitrary extensions outside that domain are immaterial.
-/

@[expose] public section

noncomputable section

open scoped NNReal

namespace KamProject.Arnold1963

/-- The real angle torus with period `2π` in each coordinate. -/
abbrev RealTorus (n : ℕ) := Fin n → AddCircle (2 * Real.pi)
/-- Real action coordinates paired with angles modulo `2π`. -/
abbrev RealPhaseSpace (n : ℕ) := RealSpace n × RealTorus n

/-- The angle displacement associated with an integer multiple of each period. -/
def angleShift {n : ℕ} (k : FourierIndex n) : ComplexSpace n :=
  complexify (fun j => 2 * Real.pi * (k j : ℝ))

/-- Invariance of a phase function under integer angle-period shifts on its domain. -/
def AnglePeriodicOn {n : ℕ} (G : Set (ComplexSpace n)) (ρ : ℝ≥0)
    (f : ComplexPhaseSpace n → ℂ) : Prop :=
  ∀ p ∈ G, ∀ q ∈ angleStrip n ρ, ∀ k : FourierIndex n,
    f (p, q + angleShift k) = f (p, q)

@[simp] theorem imagPart_add_angleShift {n : ℕ} (q : ComplexSpace n)
    (k : FourierIndex n) : imagPart (q + angleShift k) = imagPart q := by
  funext j
  simp [imagPart, angleShift, complexify]

theorem add_angleShift_mem_iff {n : ℕ} (q : ComplexSpace n) (k : FourierIndex n)
    (ρ : ℝ≥0) : q + angleShift k ∈ angleStrip n ρ ↔ q ∈ angleStrip n ρ := by
  simp [angleStrip]

end KamProject.Arnold1963
