/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Probability.CesaroWindow
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.ColoredAverage
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.RDependent

/-!
# ColoredCesaro

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The `r`-dependent Cesàro `Γ_σ` concentration engine

ABK26, proof of `l.minimal.scale.sep`, Step 1.  Step 1 does *not* end with
a fully independent family: it ends with

> "Since the sequence `{X_j}` is `r(d)`-dependent, we may apply Proposition
> `p.concentration` to obtain
> `(m−n)^{-1/2} ∑_{j=n}^m (X_j − E[X_j]) ≤ O_{Γ₂}(C c⋆^{-1} s^{-5/2} γ^{1/2})`."

`p.concentration` as printed is stated for **independent** sequences, so the
object Step 1 actually consumes is not a theorem of the manuscript.  This
module supplies it: the exact analogue of the independent Cesàro engine with
full independence weakened to the `r`-dependence of
`Algsuperdiff/Probability/RDependent.lean`.  The free `r` reaches the conclusion only
through the constant `rDepEngineConst r` (a `√(r+1)` colour count), so no
dimensional restriction rides on the engine.

## The route

Split the window `[n, m] ⊆ ℤ` into the `r+1` residue classes mod `r+1`. Two
distinct indices in one class differ by a nonzero multiple of `r+1`, hence are
`≥ r`-separated, hence the class is mutually independent
(`le_abs_sub_of_intCast_zmod_eq`); the `r+1` per-class sums are recombined by the
`Γ_σ` triangle inequality. Both halves are packaged in the palette-generic
`isBigO_gammaSigma_average_colored`, whose combinatorial input at this colouring
is `sum_sqrt_class_card_le` together with `card_zmod_succ`.

## Main results

* `rDepEngineConst` — the explicit colour-count constant.
* `isBigO_cesaroAvg_of_rDependent_centered` — colouring plus concentration for
  a centred family.
* `cesaroAvg_isBigO_of_rDependent` — the corresponding engine before centring.

## References

* ABK26, Proposition `p.concentration`.
* ABK26, `l.minimal.scale.sep`, Step 1.
-/

namespace Algsuperdiff.Probability

open MeasureTheory
open HCPolySupport.IndependentSums
open HCPolySupport.Book.Ch04 (gammaSigmaIndependentSumConst)
open scoped BigOperators

noncomputable section

/-! ## Explicit constants -/

/-- The `r`-dependent Cesàro engine constant: CoarseGraining's centered
independent-sum constant for `σ = 2`, times the centering cost, inflated by the
`Γ₂` triangle constant (recombining the `r+1` colour classes) and by `√(r+1)`
(the colour count). -/
def rDepEngineConst (r : ℕ) : ℝ :=
  gammaTriangleConst 2 * gammaSigmaIndependentSumConst 2 *
    Real.sqrt ((r : ℝ) + 1) * cesaroCenterConst 2

theorem rDepEngineConst_pos (r : ℕ) : 0 < rDepEngineConst r := by
  have h1 : 0 < gammaTriangleConst 2 := gammaTriangleConst_pos
  have h2 : 0 < gammaSigmaIndependentSumConst 2 :=
    gammaSigmaIndependentSumConst_pos (by norm_num)
  have h3 : 0 < Real.sqrt ((r : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have h4 : 0 < cesaroCenterConst 2 := cesaroCenterConst_pos (by norm_num)
  simp only [rDepEngineConst]
  exact mul_pos (mul_pos (mul_pos h1 h2) h3) h4

/-! ## The coloured concentration bound for a centred `r`-dependent family -/

section CenteredAverage

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Averaged `p.concentration` for an `r`-dependent family, in `cesaroAvg` form.**
For a centred, `r`-dependent, `Γ₂`-controlled family `{Y_j}`, the Cesàro average
over `[n, m]` obeys `O_{Γ₂}( C √(r+1) · K · (m − n + 1)^{-1/2} )`. -/
theorem isBigO_cesaroAvg_of_rDependent_centered [IsProbabilityMeasure P]
    (Y : ℤ → Ω → ℝ) {Kc : ℝ} {r : ℕ} (hKc : 0 < Kc)
    (hdep : RDependent P Y r)
    (hmeas : ∀ j, Measurable (Y j))
    (hY : ∀ j, IsBigO P (gammaSigma 2) (Y j) Kc)
    (hmean : ∀ j, ∫ ω, Y j ω ∂P = 0)
    {n m : ℤ} (hnm : n ≤ m) :
    IsBigO P (gammaSigma 2) (fun ω => cesaroAvg (fun j => Y j ω) n m)
      (gammaTriangleConst 2 * gammaSigmaIndependentSumConst 2 *
        Real.sqrt ((r : ℝ) + 1) * Kc * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2)) := by
  have hcard : (((Finset.Icc n m).card : ℕ) : ℝ) = ((m - n + 1 : ℤ) : ℝ) :=
    natCast_card_Icc_int hnm
  have hcpos : (0 : ℝ) < ((m - n + 1 : ℤ) : ℝ) := window_pos hnm
  -- Per-colour independence: same residue mod `r+1` ⇒ separation `≥ r`.
  have hIndepColor : ∀ b ∈ (Finset.Icc n m).image (fun j : ℤ => (j : ZMod (r + 1))),
      ProbabilityTheory.iIndepFun
        (fun (i : {i // i ∈ (Finset.Icc n m).filter
          (fun j : ℤ => (j : ZMod (r + 1)) = b)}) => Y i.1) P := by
    intro b _hb
    refine hdep _ ?_
    intro i hi j hj hij
    have hi' : ((i : ZMod (r + 1))) = b := (Finset.mem_filter.mp hi).2
    have hj' : ((j : ZMod (r + 1))) = b := (Finset.mem_filter.mp hj).2
    have hstep := le_abs_sub_of_intCast_zmod_eq (r := r) (by rw [hi', hj']) hij
    linarith only [hstep]
  -- The Cauchy--Schwarz input, with `colorCount = r+1`.
  have hSqrt :
      ∑ b ∈ (Finset.Icc n m).image (fun j : ℤ => (j : ZMod (r + 1))),
          Real.sqrt
            (((Finset.Icc n m).filter (fun j : ℤ => (j : ZMod (r + 1)) = b)).card : ℝ) ≤
        Real.sqrt ((r : ℝ) + 1) * Real.sqrt (((Finset.Icc n m).card : ℕ) : ℝ) := by
    have h := sum_sqrt_class_card_le (κ := ZMod (r + 1)) (Finset.Icc n m)
      (fun j : ℤ => (j : ZMod (r + 1)))
    rwa [card_zmod_succ r] at h
  have hcolored := isBigO_gammaSigma_average_colored
    (P := P) (s := Finset.Icc n m) (c := fun j : ℤ => (j : ZMod (r + 1))) (X := Y)
    (σ := 2) (K := Kc) (colorCount := (r : ℝ) + 1)
    (by norm_num) le_rfl hKc hIndepColor
    (fun i _ => hmeas i) (fun i _ => hY i) (fun i _ => hmean i) hSqrt
  -- Rewrite the averaging prefactor into `cesaroAvg` form.
  have hfun :
      (fun ω => ((((Finset.Icc n m).card : ℕ) : ℝ))⁻¹ * ∑ i ∈ Finset.Icc n m, Y i ω)
        = fun ω => cesaroAvg (fun j => Y j ω) n m := by
    funext ω
    simp only [cesaroAvg, hcard, one_div]
  -- Rewrite the scale.
  have hscale :
      gammaTriangleConst 2 * gammaSigmaIndependentSumConst 2 *
          (Real.sqrt ((r : ℝ) + 1) *
            (Real.sqrt (((Finset.Icc n m).card : ℕ) : ℝ) /
              ((((Finset.Icc n m).card : ℕ) : ℝ)))) * Kc
        = gammaTriangleConst 2 * gammaSigmaIndependentSumConst 2 *
            Real.sqrt ((r : ℝ) + 1) * Kc *
            (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2) := by
    rw [hcard, sqrt_div_self_eq_rpow_neg_half hcpos]
    ring
  rw [hfun, hscale] at hcolored
  exact hcolored

end CenteredAverage

/-! ## The engine -/

section Engine

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The `r`-dependent Cesàro concentration engine.** For an `r`-dependent family
`{X_j}` with `X_j ≤ O_{Γ₂}(K)` and `E X_j ≤ μ₀`, the Cesàro average over a window `[n, m]`
splits as `μ₀` plus a fluctuation of scale `rDepEngineConst r · K · (m − n +
1)^{-1/2}`.

This is the form Step 1 of ABK26 `l.minimal.scale.sep` needs: the same
conclusion as the fully independent engine, with independence weakened to
`r`-dependence. -/
theorem cesaroAvg_isBigO_of_rDependent [IsProbabilityMeasure P]
    (X : ℤ → Ω → ℝ) {K mu0 : ℝ} {r : ℕ} (hK : 0 < K)
    (hdep : RDependent P X r)
    (hmeas : ∀ j, Measurable (X j))
    (hX : ∀ j, IsBigO P (gammaSigma 2) (X j) K)
    (hmean : ∀ j, ∫ ω, X j ω ∂P ≤ mu0)
    (n m : ℤ) (hnm : n ≤ m) :
    ∃ Xfluc : Ω → ℝ,
      (∀ ω, cesaroAvg (fun j => X j ω) n m ≤ mu0 + Xfluc ω) ∧
      IsBigO P (gammaSigma 2) Xfluc
        (rDepEngineConst r * K * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2)) := by
  have hσ : (0 : ℝ) < 2 := by norm_num
  have hint : ∀ j, Integrable (X j) P := fun j =>
    integrable_of_isBigO_gammaSigma hσ hK (hmeas j).aemeasurable (hX j)
  have hKc : 0 < cesaroCenterConst 2 * K := mul_pos (cesaroCenterConst_pos hσ) hK
  have hYmeas : ∀ j, Measurable (fun ω => X j ω - ∫ ω', X j ω' ∂P) := fun j =>
    (hmeas j).sub measurable_const
  have hYdep : RDependent P (fun (j : ℤ) (ω : Ω) => X j ω - ∫ ω', X j ω' ∂P) r :=
    hdep.comp (fun (j : ℤ) (x : ℝ) => x - ∫ ω', X j ω' ∂P)
      (fun _ => measurable_id.sub measurable_const)
  have hYtail : ∀ j, IsBigO P (gammaSigma 2)
      (fun ω => X j ω - ∫ ω', X j ω' ∂P) (cesaroCenterConst 2 * K) := fun j =>
    centered_isBigO_gammaSigma_moment hσ hK (hmeas j).aemeasurable (hX j)
  have hYmean : ∀ j, ∫ ω, (X j ω - ∫ ω', X j ω' ∂P) ∂P = 0 := by
    intro j
    rw [MeasureTheory.integral_sub (hint j) (MeasureTheory.integrable_const _)]
    simp
  refine ⟨fun ω => cesaroAvg (fun j => X j ω - ∫ ω', X j ω' ∂P) n m, ?_, ?_⟩
  · intro ω
    exact cesaroAvg_le_add_cesaroAvg_sub (f := fun j => X j ω)
      (g := fun j => ∫ ω', X j ω' ∂P) hnm hmean
  · have hbig := isBigO_cesaroAvg_of_rDependent_centered (P := P)
      (Y := fun (j : ℤ) (ω : Ω) => X j ω - ∫ ω', X j ω' ∂P) hKc hYdep hYmeas hYtail
      hYmean hnm
    have hcst :
        gammaTriangleConst 2 * gammaSigmaIndependentSumConst 2 *
            Real.sqrt ((r : ℝ) + 1) * (cesaroCenterConst 2 * K) *
            (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2)
          = rDepEngineConst r * K * (((m - n + 1 : ℤ) : ℝ)) ^ (-(1 : ℝ) / 2) := by
      simp only [rDepEngineConst]; ring
    rwa [hcst] at hbig

end Engine

end

end Algsuperdiff.Probability
