/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineResidueLevel

/-!
# HomSchauderUniform

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `s`-UNIFORM Schauder constant, and the `K_abs` frame condition it closes

## The trap

The §4.5 Step-4 Schauder constant `C_S4(d,s)` is a `Classical.choose` of an
`s`-indexed existential.  Its defining property is UPWARD CLOSED in the
constant, so nothing in the tree bounds the chosen value: the frame condition

```text
  spineClauseConst d s p C_w (C_S4 d s) ≤ K_abs
```

can be met at each fixed `s`, but NOT by one `K_abs` produced before the model
— and at the §4.5 pin `s = |log γ|⁻¹` the exponent is a function of the model.
That is a genuine obstruction to Theorem B's constant scope, not a bookkeeping
nuisance.

## The `s = 1/2` reduction

The underlying producer's constant does not depend on `s` at all
(`Section4.Provider.Schauder.cube_schauder_of_zeroDatumCubeSchauder` returns
`2·C₀ + 1` with `C₀` the zero-datum constant), and the `s`-package is in any
case a consequence of the `s = 1/2` package on a triadic cube: on `□_m` the two
points of a Hölder difference are at distance at most `3^m`, so

```text
  [f]_{C^{0,s}(□_m)} ≤ 3^{m(1/2 - s)} [f]_{C^{0,1/2}(□_m)},
```

and the target's own weight `3^{-sm}` absorbs the factor EXACTLY: multiplying
the `s = 1/2` gauge estimate by `3^{m(1/2-s)}` turns
`3^{-m/2}K_sup + K_Höl ≤ C 3^{-m/2} ⟨data⟩` into
`3^{-sm}K_sup + 3^{m(1/2-s)}K_Höl ≤ C 3^{-sm} ⟨data⟩`, with the SAME `C`.

`exists_comparator_schauder_package_uniform` is that statement, and
`stepFourSchauderConstU d` is its `s`-free constant.  `spineClauseConst_le_abs`
then closes the frame condition at a `K_abs` naming only `d` and an envelope
for `C_w` — both available before the model.

## Scope

The §4.5 bundle core refers to `C_S4(d, s.1)` inside its `hKabs` conjunct, so
consuming the uniform constant requires a SIBLING of that bundle (and of the
re-cut's two consumption sites, which spend `hKabs` through `spineClauseConst`)
with `C_S4(d, s.1)` replaced by `stepFourSchauderConstU d`. That re-cut is NOT performed here;
what is proved here is that the replacement is sound — the uniform constant
satisfies the same package at every admissible `s`.
-/

open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support

namespace Algsuperdiff.Section4.Provider.Homogenization

noncomputable section

variable {d : ℕ}

/-! ## 1. The Hölder order step -/

/-- `Real.rpow`-shaped exponent addition at base `3`: stated with `Real.rpow`
applied, which is the form the gauge's own definition uses. -/
private theorem rpow_three_mul_rpow_three (y z : ℝ) :
    Real.rpow 3 y * Real.rpow 3 z = Real.rpow 3 (y + z) :=
  (Real.rpow_add (by norm_num : (0 : ℝ) < 3) y z).symm

/-- **The Hölder order step on a bounded set.**  Lowering the exponent from
`α` to `β ≤ α` costs exactly the `(α-β)`-th power of the diameter. -/
theorem holderSeminormBoundOn_order_le {U : Set (Vec d)} {alpha beta K D : ℝ}
    {f : Vec d → Vec d} (hle : beta ≤ alpha) (hK : 0 ≤ K)
    (hD : 0 < D) (hdiam : ∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ D)
    (h : HolderSeminormBoundOn U alpha K f) :
    HolderSeminormBoundOn U beta (K * D ^ (alpha - beta)) f := by
  intro x hx y hy
  rcases eq_or_lt_of_le (norm_nonneg (x - y)) with hzero | hpos
  · have hxy : x = y := sub_eq_zero.mp (norm_eq_zero.mp hzero.symm)
    have hKD : (0 : ℝ) ≤ K * D ^ (alpha - beta) :=
      mul_nonneg hK (Real.rpow_nonneg hD.le _)
    have hnn : (0 : ℝ) ≤ ‖x - y‖ ^ beta := Real.rpow_nonneg (norm_nonneg _) _
    have hzz : ‖f x - f y‖ = 0 := by rw [hxy, sub_self, norm_zero]
    rw [hzz]
    exact mul_nonneg hKD hnn
  · have hsplit : ‖x - y‖ ^ alpha = ‖x - y‖ ^ (alpha - beta) * ‖x - y‖ ^ beta := by
      rw [← Real.rpow_add hpos]
      congr 1
      ring
    have hdle : ‖x - y‖ ^ (alpha - beta) ≤ D ^ (alpha - beta) :=
      Real.rpow_le_rpow (norm_nonneg _) (hdiam x hx y hy) (by linarith only [hle])
    have hbnn : (0 : ℝ) ≤ ‖x - y‖ ^ beta := Real.rpow_nonneg (norm_nonneg _) _
    calc ‖f x - f y‖ ≤ K * ‖x - y‖ ^ alpha := h x hx y hy
      _ = K * ‖x - y‖ ^ (alpha - beta) * ‖x - y‖ ^ beta := by rw [hsplit]; ring
      _ ≤ K * D ^ (alpha - beta) * ‖x - y‖ ^ beta :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hdle hK) hbnn

/-! ## 2. The `s`-uniform package -/

/-- **THE `s`-UNIFORM SCHAUDER PACKAGE.**

One constant, produced before the exponent `s`, the scale `m`, the diffusivity
and the data, serving the whole admissible range `0 < s ≤ 1/2`: the comparator
of `HomStepFourSchauder.exists_comparator_schauder_package` at the SAME
constant for every `s`.

The proof runs the `s = 1/2` package once and lowers the Hölder exponent on
`□_m`; the loss `3^{m(1/2-s)}` is exactly cancelled by the gauge's own
`3^{-sm}`, so no constant is spent. -/
theorem exists_comparator_schauder_package_uniform (dimension : 2 ≤ d) :
    ∃ Csch : ℝ, 0 < Csch ∧
      ∀ s : ℝ, 0 < s → s ≤ 1 / 2 →
        ∀ (m : ℤ) (sigma : ℝ), 0 < sigma →
          ∀ (g : Vec d → Vec d) (h : H1Function (openCubeSet (originCube d m)))
            (Kg KhInf Kh : ℝ),
            HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
            (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
            HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
            ∃ v : H1Function (openCubeSet (originCube d m)),
              IsDirichletSolutionOn (fun _ => sigma • (1 : Mat d)) (originCube d m) v h g ∧
              ∃ Ksup KHol : ℝ, 0 ≤ Ksup ∧ 0 ≤ KHol ∧
                (∀ x ∈ openCubeSet (originCube d m), ‖v.grad x‖ ≤ Ksup) ∧
                HolderSeminormBoundOn (openCubeSet (originCube d m)) s KHol v.grad ∧
                wsInftyGauge (originCube d m) s Ksup KHol ≤
                  Csch * (Real.rpow 3 (s * (m : ℝ)))⁻¹ *
                    dataBracket sigma (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh := by
  obtain ⟨Csch, hCsch, H⟩ :=
    exists_comparator_schauder_package (d := d) dimension (s := 1 / 2) (by norm_num) le_rfl
  refine ⟨Csch, hCsch, ?_⟩
  intro s hs0 hs2 m sigma hsigma g h Kg KhInf Kh hKg hKhInf hKh
  obtain ⟨v, hsol, Ksup, KHol, hKsup, hKHol, hb, hH, hgauge⟩ :=
    H m sigma hsigma g h Kg KhInf Kh hKg hKhInf hKh
  /- the transported Hölder consta -/
  have hDpos : (0 : ℝ) < Real.rpow 3 ((m : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hdiam : ∀ x ∈ openCubeSet (originCube d m), ∀ y ∈ openCubeSet (originCube d m),
      ‖x - y‖ ≤ Real.rpow 3 ((m : ℝ)) := fun x hx y hy =>
    norm_sub_le_cubeScaleFactor (originCube d m) x
      (openCubeSet_subset_closedCubeSet _ hx) y (openCubeSet_subset_closedCubeSet _ hy)
  have hHs : HolderSeminormBoundOn (openCubeSet (originCube d m)) s
      (KHol * Real.rpow 3 ((m : ℝ)) ^ (1 / 2 - s)) v.grad :=
    holderSeminormBoundOn_order_le hs2 hKHol hDpos hdiam hH
  /- the gauge, multiplied by the SAME fact -/
  set A : ℝ := Real.rpow 3 ((m : ℝ) * (1 / 2 - s)) with hA
  have hApos : (0 : ℝ) < A := Real.rpow_pos_of_pos (by norm_num) _
  have hAeq : Real.rpow 3 ((m : ℝ)) ^ (1 / 2 - s) = A :=
    (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) (m : ℝ) (1 / 2 - s)).symm
  have hmul := mul_le_mul_of_nonneg_left hgauge hApos.le
  have hcomb : A * Real.rpow 3 (-((1 / 2 : ℝ) * (m : ℝ))) =
      Real.rpow 3 (-(s * (m : ℝ))) := by
    rw [hA, rpow_three_mul_rpow_three]
    congr 1
    ring
  have hleft : A * wsInftyGauge (originCube d m) (1 / 2) Ksup KHol =
      wsInftyGauge (originCube d m) s Ksup (KHol * A) := by
    change A * (Real.rpow 3 (-((1 / 2 : ℝ) * (m : ℝ))) * Ksup + KHol) =
      Real.rpow 3 (-(s * (m : ℝ))) * Ksup + KHol * A
    calc A * (Real.rpow 3 (-((1 / 2 : ℝ) * (m : ℝ))) * Ksup + KHol)
        = A * Real.rpow 3 (-((1 / 2 : ℝ) * (m : ℝ))) * Ksup + KHol * A := by ring
      _ = Real.rpow 3 (-(s * (m : ℝ))) * Ksup + KHol * A := by rw [hcomb]
  have hright : A * (Csch * (Real.rpow 3 ((1 / 2 : ℝ) * (m : ℝ)))⁻¹ *
        dataBracket sigma (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh) =
      Csch * (Real.rpow 3 (s * (m : ℝ)))⁻¹ *
        dataBracket sigma (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh := by
    have hinv : (Real.rpow 3 ((1 / 2 : ℝ) * (m : ℝ)))⁻¹ =
        Real.rpow 3 (-((1 / 2 : ℝ) * (m : ℝ))) :=
      (Real.rpow_neg (by norm_num) _).symm
    have hinv2 : (Real.rpow 3 (s * (m : ℝ)))⁻¹ = Real.rpow 3 (-(s * (m : ℝ))) :=
      (Real.rpow_neg (by norm_num) _).symm
    rw [hinv, hinv2]
    calc A * (Csch * Real.rpow 3 (-((1 / 2 : ℝ) * (m : ℝ))) *
          dataBracket sigma (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh)
        = Csch * (A * Real.rpow 3 (-((1 / 2 : ℝ) * (m : ℝ)))) *
            dataBracket sigma (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh := by ring
      _ = Csch * Real.rpow 3 (-(s * (m : ℝ))) *
            dataBracket sigma (Real.rpow 3 ((m : ℝ) / 2)) Kg KhInf Kh := by rw [hcomb]
  refine ⟨v, hsol, Ksup, KHol * A, hKsup, mul_nonneg hKHol hApos.le, hb, ?_, ?_⟩
  · rw [hAeq] at hHs; exact hHs
  · rw [← hleft, ← hright]
    exact hmul

/-! ## 3. The `s`-free constant and the `K_abs` closure -/

/-- **THE `s`-UNIFORM SCHAUDER CONSTANT.**  Unlike the `s`-indexed Step-4
Schauder constant, this is a `Classical.choose` of an `s`-FREE existential, so it
is a function of `d` alone. -/
def stepFourSchauderConstU (d : ℕ) : ℝ :=
  if h : 2 ≤ d then Classical.choose (exists_comparator_schauder_package_uniform (d := d) h)
  else 0

theorem stepFourSchauderConstU_pos (hd : 2 ≤ d) : 0 < stepFourSchauderConstU d := by
  rw [stepFourSchauderConstU, dite_eq_left hd]
  exact (Classical.choose_spec (exists_comparator_schauder_package_uniform (d := d) hd)).1

theorem stepFourSchauderConstU_nonneg (d : ℕ) : 0 ≤ stepFourSchauderConstU d := by
  by_cases hd : 2 ≤ d
  · exact (stepFourSchauderConstU_pos hd).le
  · rw [stepFourSchauderConstU, dite_eq_right hd]

/-- **THE `K_abs` FRAME CONDITION, CLOSED BEFORE THE MODEL.**

At the uniform Schauder constant, the absorbed-constant condition of the re-cut
bundle holds at

```text
  K_abs:= (2 · stepFourSchauderConstU d + 288 d²) · C_w⁰,
```

which names only the dimension and an envelope `C_w⁰` for the pairing constant
— no `s`, hence no model.  The only `s`-dependence of `spineClauseConst` is the
lifting factor `liftGeomFactor (s + d/p)`, and the bundle's OWN guard
`s + d/p ≤ 1/2` bounds it by `3`. -/
theorem spineClauseConst_le_abs (d : ℕ) {s p Cw Cw0 : ℝ} (hCw : 0 ≤ Cw)
    (hCwle : Cw ≤ Cw0) (hguard : s + (d : ℝ) / p ≤ 1 / 2) :
    spineClauseConst d s p Cw (stepFourSchauderConstU d) ≤
      (2 * stepFourSchauderConstU d + 288 * (d : ℝ) ^ (2 : ℕ)) * Cw0 := by
  have hU : (0 : ℝ) ≤ stepFourSchauderConstU d := stepFourSchauderConstU_nonneg d
  have hlift : liftGeomFactor (s + (d : ℝ) / p) ≤ 3 := liftGeomFactor_le_three hguard
  have hlift0 : (0 : ℝ) ≤ liftGeomFactor (s + (d : ℝ) / p) :=
    liftGeomFactor_nonneg (by linarith only [hguard])
  have hd2 : (0 : ℝ) ≤ 96 * (d : ℝ) ^ (2 : ℕ) := by positivity
  have hstep : 96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) ≤
      288 * (d : ℝ) ^ (2 : ℕ) := by
    have := mul_le_mul_of_nonneg_left hlift hd2
    linarith only [this]
  have hCw0 : (0 : ℝ) ≤ Cw0 := le_trans hCw hCwle
  have hsum : (2 : ℝ) * stepFourSchauderConstU d +
      96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) ≤
      2 * stepFourSchauderConstU d + 288 * (d : ℝ) ^ (2 : ℕ) := by
    linarith only [hstep]
  have hsum0 : (0 : ℝ) ≤ 2 * stepFourSchauderConstU d +
      96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) := by
    have h1 : (0 : ℝ) ≤ 2 * stepFourSchauderConstU d := by linarith only [hU]
    have h2 : (0 : ℝ) ≤ 96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p) :=
      mul_nonneg hd2 hlift0
    linarith only [h1, h2]
  calc spineClauseConst d s p Cw (stepFourSchauderConstU d)
      = (2 * stepFourSchauderConstU d +
          96 * (d : ℝ) ^ (2 : ℕ) * liftGeomFactor (s + (d : ℝ) / p)) * Cw := by
        rw [spineClauseConst]; ring
    _ ≤ (2 * stepFourSchauderConstU d + 288 * (d : ℝ) ^ (2 : ℕ)) * Cw :=
        mul_le_mul_of_nonneg_right hsum hCw
    _ ≤ (2 * stepFourSchauderConstU d + 288 * (d : ℝ) ^ (2 : ℕ)) * Cw0 :=
        mul_le_mul_of_nonneg_left hCwle (by linarith only [hsum0, hstep])

end

end Algsuperdiff.Section4.Provider.Homogenization
