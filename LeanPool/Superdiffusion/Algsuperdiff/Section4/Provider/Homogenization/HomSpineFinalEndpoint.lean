/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineFinalWitness
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomFinitePSource
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomStepFourSchauder

/-!
# HomSpineFinalEndpoint

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5: THE SPINE — the frozen root's conclusion body

```text
  ∃ γ₀ C, 0 < γ₀ ∧ 0 < C ∧ ∀ M, c⋆(M) = c⋆ → γ ≤ γ₀ → ∀ m,
    ∃ σ_m, 0 < σ_m ∧ (C1) ∧
      ∃ E_B, (0 ≤ E_B) ∧ Measurable E_B ∧ (C2) ∧
        ∀ᵐ ω, ∀ L ≥ m, ∀ u v h g K_g K_h K_h^∞, (five binders) → (C3) ∧ (C4).
```

## What is DISCHARGED here, and what is supplied

* **(C1)** — the `σ_m` closeness display: supplied at the constant `C_flow`
  and re-based to the endpoint's own `C = C_wit + C_flow`.  This is Section 3's
  `diffusivity_asymptotics` (`Frozen/Section3/DiffusivityAsymptotics.lean`) read
  at `σ_m = Annealed.sigmaBar M m`; the endpoint is stated for an ARBITRARY
  `σ_m` satisfying it, so the Section-3 anchor plugs in unchanged, and so does
  the trivial witness `σ_m = √(ν² + c⋆γ⁻¹3^{2γm})` (for which the display holds
  at every `C ≥ 0`).  Nothing about `σ_m` is assumed beyond positivity and that
  one display.
* **(C2)** — the real cut `E_B = K·(EthmB(m)).toReal`, its measurability, its
  moment at the root's own constant shape and `p`-range.  Its own single edge is
  `hY`.
* **(C3), (C4)** — supplied per `ω` by the clause supplier, at the
  `EthmB(m)`-domination interface: the producer exhibits a REAL defect `D` with
  `ofReal D ≤ EthmB(m)(ω)` (this is the manuscript's "comparing to the
  definition of `EthmB(m)`") and the two printed displays at `K·D`.
  The endpoint converts `K·D` into `E_B(ω)` through the witness's linkage —
  which is where the a.e. finiteness of the `[0,∞]` carrier is spent — and
  produces the root's clause bodies verbatim.

## The data-bracket nonnegativity, derived (not assumed)

The `stepFourEnergyEndpoint` carries `0 ≤ dataBracket …` as a binder.  Here it
is PROVED from the root's own five binders: `□_m` contains two distinct points
(`exists_ne_pair_openCubeSet`), so `HolderSeminormBoundOn.nonneg` gives `0 ≤
K_g` and `0 ≤ K_h`, and the sup binder at the cube centre gives `0 ≤ K_h^∞`.
No frame item is left on the data side.

## The conditional set of the spine endpoint, itemized

1. `hY` — the Theorem-C minimal-scale exponential moment (`hC`), exactly the
   edge, at the abstract `[0,∞]` carrier.  See `HomSpineFinalWitness` for the
   blocked composition with the `homY_moment_bound_of_gamma_le` (a NAME
   COLLISION in the tree, reported there).
2. `hC1` — the `σ_m` closeness display (Section 3's own anchor, or the trivial
   witness).
3. `hclauses` — the per-`ω` clause supplier.  `HomSpineFinalStepFour`'s
   `exists_comparator_stepFourEnergy` produces its (C4) half from ONE `hCG'`
   application and the Schauder external; its (C3) half is the
   `L^∞` conversion at the same `hCG'`.  What is NOT bridged here is
   the comparator quantifier (`∃ v` produced by the Schauder package versus the
   root's `∀ v`) and the `hlevel`/`hS` arithmetic that consumes `hC`'s display;
   both are itemized in this file.
-/

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. Two distinct points of an open cube -/

/-- An open triadic cube in dimension `d ≥ 1` contains two distinct points: its
centre and the centre shifted by half a radius in every coordinate.  This is all
that is needed to turn the root's Hölder binders into `0 ≤ K_g`, `0 ≤ K_h`. -/
theorem exists_ne_pair_openCubeSet [NeZero d] (Q : TriadicCube d) :
    ∃ x y : Vec d, x ∈ openCubeSet Q ∧ y ∈ openCubeSet Q ∧ x ≠ y := by
  have hr : 0 < cubeRadius Q := cubeRadius_pos Q
  have hi0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  refine ⟨cubeCenter Q, fun i => cubeCenter Q i + cubeRadius Q / 2, ?_, ?_, ?_⟩
  · rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self hr
  · rw [← ball_cubeCenter_eq_openCubeSet, Metric.mem_ball, dist_pi_lt_iff hr]
    intro i
    have hval : cubeCenter Q i + cubeRadius Q / 2 - cubeCenter Q i = cubeRadius Q / 2 := by
      ring
    rw [Real.dist_eq, hval, abs_of_pos (by linarith only [hr])]
    linarith only [hr]
  · intro hcon
    have h0 : cubeCenter Q ⟨0, hi0⟩ = cubeCenter Q ⟨0, hi0⟩ + cubeRadius Q / 2 :=
      congrFun hcon ⟨0, hi0⟩
    linarith only [hr, h0]

/-- The printed data bracket is nonnegative under the root's own five binders. -/
theorem dataBracket_nonneg_of_binders [NeZero d] {m : ℤ} {sigmaBarM Kg Kh KhInf : ℝ}
    {h : H1Function (openCubeSet (originCube d m))} {g : Vec d → Vec d}
    (hsig : 0 < sigmaBarM)
    (hKg : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g)
    (hKh : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad)
    (hKhInf : ∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) :
    0 ≤ dataBracket sigmaBarM (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh := by
  obtain ⟨x0, y0, hx0, hy0, hne⟩ := exists_ne_pair_openCubeSet (originCube d m)
  have hKg0 : 0 ≤ Kg := hKg.nonneg hx0 hy0 hne
  have hKh0 : 0 ≤ Kh := hKh.nonneg hx0 hy0 hne
  have hKhInf0 : 0 ≤ KhInf := le_trans (norm_nonneg _) (hKhInf x0 hx0)
  have hpow : (0 : ℝ) ≤ Real.rpow 3 ((m : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have h1 : (0 : ℝ) ≤ sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr hsig.le) hpow) hKg0
  have h2 : (0 : ℝ) ≤ Real.rpow 3 ((m : ℝ) / 2) * Kh := mul_nonneg hpow hKh0
  rw [dataBracket]
  linarith only [h1, h2, hKhInf0]

end

end Algsuperdiff.Section4.Provider.Homogenization
