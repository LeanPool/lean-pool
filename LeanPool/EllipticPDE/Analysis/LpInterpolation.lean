/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity


/-!
# Interpolation of `Lᵖ` seminorms

For an exponent `q` between `r` and `s`, with `1/q = θ/r + (1-θ)/s` and `θ ∈ (0,1)`, the `L^q`
seminorm is bounded by the geometric mean

`‖f‖_q ≤ ‖f‖_r^θ ‖f‖_s^{1-θ}`.

The proof is Hölder's inequality applied to the splitting `|f|^q = |f|^{qθ} · |f|^{q(1-θ)}` at the
conjugate pair `r/(qθ)` and `s/(q(1-θ))`, whose reciprocals sum to `q(θ/r + (1-θ)/s) = 1`.

Mathlib's `Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean` supplies Hölder's inequality
and the bounds that compare two exponents on a finite measure, and stops short of this one.

The consumer is compactness of the Sobolev embedding below the critical exponent: a sequence
converging in `L²` and bounded in `L^{2⋆}` converges at every exponent between them, which is the
step Guo's proof of Rellich-Kondrachov takes between `L¹` and `L^{p⋆}`.

## Main declarations

* `EllipticPdes.Analysis.eLpNorm_le_rpow_mul_rpow`: the interpolation inequality.
* `EllipticPdes.Analysis.eLpNorm_le_of_le_of_le`: the form the compactness argument uses, bounding
  the `L^q` seminorm by a bound at each end.

## References

Y. Guo, *Partial Differential Equations*, proof of Theorem IV.2.10; H. Brezis, *Functional
Analysis, Sobolev Spaces and Partial Differential Equations*, Remark 2 after Theorem 4.16.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace EllipticPdes.Analysis

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] {f : α → E}

/-- **Interpolation of `Lᵖ` seminorms.** With `1/q = θ/r + (1-θ)/s` and `θ ∈ (0,1)`, the `L^q`
seminorm is bounded by the geometric mean of the seminorms at `r` and at `s`. -/
theorem eLpNorm_le_rpow_mul_rpow {r s q : ℝ≥0∞} (hr : r ≠ 0) (hr' : r ≠ ∞)
    (hs : s ≠ 0) (hs' : s ≠ ∞) (hq : q ≠ 0) (hq' : q ≠ ∞) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hqrs : q.toReal⁻¹ = θ * r.toReal⁻¹ + (1 - θ) * s.toReal⁻¹)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f q μ ≤ eLpNorm f r μ ^ θ * eLpNorm f s μ ^ (1 - θ) := by
  have hQ : 0 < q.toReal := ENNReal.toReal_pos hq hq'
  have hR : 0 < r.toReal := ENNReal.toReal_pos hr hr'
  have hS : 0 < s.toReal := ENNReal.toReal_pos hs hs'
  have hθ1' : 0 < 1 - θ := by linarith
  have hQθ : 0 < q.toReal * θ := by positivity
  have hQθ' : 0 < q.toReal * (1 - θ) := by positivity
  -- The conjugate pair the splitting is tested against.
  set ea : ℝ≥0∞ := ENNReal.ofReal (r.toReal / (q.toReal * θ)) with hea
  set eb : ℝ≥0∞ := ENNReal.ofReal (s.toReal / (q.toReal * (1 - θ))) with heb
  have hainv : ea⁻¹ = ENNReal.ofReal (q.toReal * θ / r.toReal) := by
    rw [hea, ← ENNReal.ofReal_inv_of_pos (by positivity), inv_div]
  have hbinv : eb⁻¹ = ENNReal.ofReal (q.toReal * (1 - θ) / s.toReal) := by
    rw [heb, ← ENNReal.ofReal_inv_of_pos (by positivity), inv_div]
  have : ENNReal.HolderTriple ea eb 1 := by
    refine ⟨?_⟩
    rw [hainv, hbinv, ← ENNReal.ofReal_add (by positivity) (by positivity), inv_one]
    rw [show q.toReal * θ / r.toReal + q.toReal * (1 - θ) / s.toReal = 1 by
      field_simp at hqrs ⊢
      nlinarith [hqrs, hQ, hR, hS]]
    simp
  -- The two factors of the splitting.
  have hg : AEStronglyMeasurable (fun x => ‖f x‖ ^ (q.toReal * θ)) μ :=
    (Real.continuous_rpow_const hQθ.le).comp_aestronglyMeasurable hf.norm
  have hh : AEStronglyMeasurable (fun x => ‖f x‖ ^ (q.toReal * (1 - θ))) μ :=
    (Real.continuous_rpow_const hQθ'.le).comp_aestronglyMeasurable hf.norm
  have hsplit : ∀ x, ‖f x‖ ^ q.toReal
      = ‖f x‖ ^ (q.toReal * θ) * ‖f x‖ ^ (q.toReal * (1 - θ)) := by
    intro x
    rw [← Real.rpow_add' (norm_nonneg _) (by nlinarith)]
    ring_nf
  -- Hölder against that pair.
  have hHolder := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (μ := μ) (p := ea) (q := eb) (r := 1)
    (f := fun x => ‖f x‖ ^ (q.toReal * θ)) (g := fun x => ‖f x‖ ^ (q.toReal * (1 - θ)))
    (fun u v => u * v) 1 (continuous_fst.mul continuous_snd) hg hh
    (Filter.Eventually.of_forall (fun x => by
      simp only [nnnorm_mul, one_mul]
      exact le_rfl))
  -- Read each seminorm back as one of `f`.
  have hLHS : eLpNorm (fun x => ‖f x‖ ^ (q.toReal * θ) * ‖f x‖ ^ (q.toReal * (1 - θ))) 1 μ
      = eLpNorm f q μ ^ q.toReal := by
    rw [eLpNorm_congr_ae (Filter.EventuallyEq.of_eq (funext fun x => (hsplit x).symm)),
      eLpNorm_norm_rpow f hf hQ, one_mul, ENNReal.ofReal_toReal hq']
  have hA : eLpNorm (fun x => ‖f x‖ ^ (q.toReal * θ)) ea μ = eLpNorm f r μ ^ (q.toReal * θ) := by
    rw [eLpNorm_norm_rpow f hf hQθ, hea, ← ENNReal.ofReal_mul (by positivity),
      div_mul_cancel₀ _ (ne_of_gt hQθ), ENNReal.ofReal_toReal hr']
  have hB : eLpNorm (fun x => ‖f x‖ ^ (q.toReal * (1 - θ))) eb μ
      = eLpNorm f s μ ^ (q.toReal * (1 - θ)) := by
    rw [eLpNorm_norm_rpow f hf hQθ', heb, ← ENNReal.ofReal_mul (by positivity),
      div_mul_cancel₀ _ (ne_of_gt hQθ'), ENNReal.ofReal_toReal hs']
  rw [hLHS, hA, hB, ENNReal.coe_one, one_mul] at hHolder
  -- Take the `q`-th root.
  refine (ENNReal.rpow_le_rpow_iff hQ).mp ?_
  refine hHolder.trans_eq ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ hQ.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    mul_comm θ q.toReal, mul_comm (1 - θ) q.toReal]

/-- The form the compactness argument uses: a bound at each end bounds the middle. -/
theorem eLpNorm_le_of_le_of_le {r s q : ℝ≥0∞} (hr : r ≠ 0) (hr' : r ≠ ∞)
    (hs : s ≠ 0) (hs' : s ≠ ∞) (hq : q ≠ 0) (hq' : q ≠ ∞) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hqrs : q.toReal⁻¹ = θ * r.toReal⁻¹ + (1 - θ) * s.toReal⁻¹)
    (hf : AEStronglyMeasurable f μ) {A B : ℝ≥0∞}
    (hA : eLpNorm f r μ ≤ A) (hB : eLpNorm f s μ ≤ B) :
    eLpNorm f q μ ≤ A ^ θ * B ^ (1 - θ) := by
  refine (eLpNorm_le_rpow_mul_rpow hr hr' hs hs' hq hq' hθ0 hθ1 hqrs hf).trans ?_
  exact mul_le_mul' (ENNReal.rpow_le_rpow hA hθ0.le)
    (ENNReal.rpow_le_rpow hB (by linarith))

end EllipticPdes.Analysis
