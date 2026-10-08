/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.AnalyticCarriers
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.BasicLemmas

/-!
# High-contrast homogenization: Analytic.WeightedEnergy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The weighted Dirichlet energy against the unweighted one

The energy `sEnergyOn b V F = ∫_V F · s F` of the coefficient-weighted spaces of
`s.introduction` is the Lebesgue integral of the quadratic form
of the symmetric part `s` of the coefficient field.  Where the field is
uniformly elliptic almost everywhere on the set the integral runs over, the
quadratic form is pinched between `lam ‖F‖²` and `Lam ‖F‖²` pointwise a.e. on
that set, so the weighted energy is two-sided comparable to the unweighted one
and is finite exactly when `F ∈ L²(V)`.  The constants are those of `V`; each
comparison is stated first for the pinching restricted to `V`, and the form with
a pinching on all of `ℝ^d` follows by restriction.  The
identity that lets the skew part drop out of the quadratic form is
`vecDot_matVecMul_symmPart`, already in CoarseGraining.

Neither half of the comparison uses any measurability, of `b` or of `F`: both
are pointwise a.e. comparisons of Lebesgue integrals.  Measurability enters only
where the `ℝ≥0∞` finiteness statement is turned into Bochner square
integrability, which is the form the pairing estimates consume.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The lower half of the comparison, with the pinching read on `V` alone:
`lam ∫_V ‖F‖² ≤ ∫_V F · s F`. -/
theorem lintegral_ofReal_vecNormSq_le_sEnergyOn_restrict {b : CoeffField d}
    {V : Set (Vec d)} {lam Lam : ℝ}
    (hell : ∀ᵐ x ∂volume.restrict V, IsEllipticMatrix lam Lam (b x))
    (F : Vec d → Vec d) :
    ENNReal.ofReal lam * (∫⁻ x in V, ENNReal.ofReal (vecNormSq (F x)) ∂volume) ≤
      sEnergyOn b V F := by
  simp only [sEnergyOn]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [hell] with x hx
  rw [← ENNReal.ofReal_mul hx.1.le]
  exact ENNReal.ofReal_le_ofReal (lowerBound_symmPart_of_isEllipticMatrix hx (F x))

/-- The lower half of the comparison: `lam ∫_V ‖F‖² ≤ ∫_V F · s F`. -/
theorem lintegral_ofReal_vecNormSq_le_sEnergyOn {b : CoeffField d}
    {V : Set (Vec d)} {lam Lam : ℝ}
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x)) (F : Vec d → Vec d) :
    ENNReal.ofReal lam * (∫⁻ x in V, ENNReal.ofReal (vecNormSq (F x)) ∂volume) ≤
      sEnergyOn b V F :=
  lintegral_ofReal_vecNormSq_le_sEnergyOn_restrict (Lam := Lam)
    (ae_restrict_of_ae hell) F

/-- The upper half of the comparison, with the pinching read on `V` alone:
`∫_V F · s F ≤ Lam ∫_V ‖F‖²`. -/
theorem sEnergyOn_le_lintegral_ofReal_vecNormSq_restrict {b : CoeffField d}
    {V : Set (Vec d)} {lam Lam : ℝ}
    (hell : ∀ᵐ x ∂volume.restrict V, IsEllipticMatrix lam Lam (b x))
    (F : Vec d → Vec d) :
    sEnergyOn b V F ≤
      ENNReal.ofReal Lam * (∫⁻ x in V, ENNReal.ofReal (vecNormSq (F x)) ∂volume) := by
  simp only [sEnergyOn]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [hell] with x hx
  rw [← ENNReal.ofReal_mul (hx.1.le.trans hx.2.1)]
  exact ENNReal.ofReal_le_ofReal (upperBound_symmPart_of_isEllipticMatrix hx (F x))

/-- The upper half of the comparison: `∫_V F · s F ≤ Lam ∫_V ‖F‖²`. -/
theorem sEnergyOn_le_lintegral_ofReal_vecNormSq {b : CoeffField d}
    {V : Set (Vec d)} {lam Lam : ℝ}
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x)) (F : Vec d → Vec d) :
    sEnergyOn b V F ≤
      ENNReal.ofReal Lam * (∫⁻ x in V, ENNReal.ofReal (vecNormSq (F x)) ∂volume) :=
  sEnergyOn_le_lintegral_ofReal_vecNormSq_restrict (lam := lam)
    (ae_restrict_of_ae hell) F

/-- **The weighted energy is finite exactly when the field is in `L²`**, with the
pinching read on `V` alone.  No measurability of `b` or of `F` is used: both
halves are pointwise a.e. comparisons of Lebesgue integrals. -/
theorem sEnergyOn_ne_top_iff_restrict {b : CoeffField d} {V : Set (Vec d)}
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume.restrict V, IsEllipticMatrix lam Lam (b x))
    (F : Vec d → Vec d) :
    sEnergyOn b V F ≠ ⊤ ↔
      (∫⁻ x in V, ENNReal.ofReal (vecNormSq (F x)) ∂volume) ≠ ⊤ := by
  have hlam0 : ENNReal.ofReal lam ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hlam
  constructor
  · intro h hcon
    have hlow :=
      lintegral_ofReal_vecNormSq_le_sEnergyOn_restrict (V := V) (Lam := Lam) hell F
    rw [hcon, ENNReal.mul_top hlam0] at hlow
    exact h (top_le_iff.mp hlow)
  · intro h
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h)
      (sEnergyOn_le_lintegral_ofReal_vecNormSq_restrict (lam := lam) hell F)

/-- **The weighted energy is finite exactly when the field is in `L²`.**  No
measurability of `b` or of `F` is used: both halves are pointwise a.e.
comparisons of Lebesgue integrals. -/
theorem sEnergyOn_ne_top_iff {b : CoeffField d} {V : Set (Vec d)} {lam Lam : ℝ}
    (hlam : 0 < lam) (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    (F : Vec d → Vec d) :
    sEnergyOn b V F ≠ ⊤ ↔
      (∫⁻ x in V, ENNReal.ofReal (vecNormSq (F x)) ∂volume) ≠ ⊤ :=
  sEnergyOn_ne_top_iff_restrict (Lam := Lam) hlam (ae_restrict_of_ae hell) F

/-- Measurability of the squared Euclidean norm of a vector field, from
measurability of its components. -/
theorem aestronglyMeasurable_vecNormSq {μ : Measure (Vec d)} {F : Vec d → Vec d}
    (hF : ∀ j, AEStronglyMeasurable (fun x => F x j) μ) :
    AEStronglyMeasurable (fun x => vecNormSq (F x)) μ := by
  have h : (fun x => vecNormSq (F x)) =
      ∑ j : Fin d, fun x : Vec d => F x j * F x j := by
    funext x
    simp [vecNormSq, vecDot, Finset.sum_apply]
  rw [h]
  exact Finset.aestronglyMeasurable_sum _ fun j _ => (hF j).mul (hF j)

/-- The `ℝ≥0∞` finiteness statement and Bochner square integrability agree. -/
theorem integrableOn_vecNormSq_iff_lintegral_ne_top {V : Set (Vec d)}
    {F : Vec d → Vec d}
    (hF : ∀ j, AEStronglyMeasurable (fun x => F x j) (volume.restrict V)) :
    IntegrableOn (fun x => vecNormSq (F x)) V volume ↔
      (∫⁻ x in V, ENNReal.ofReal (vecNormSq (F x)) ∂volume) ≠ ⊤ :=
  (lintegral_ofReal_ne_top_iff_integrable (aestronglyMeasurable_vecNormSq hF)
    (Filter.Eventually.of_forall fun x => vecNormSq_nonneg (F x))).symm

/-- **Finite weighted energy forces `F ∈ L²(V)`**, with the pinching read on `V`
alone; this is the hypothesis the absolute convergence of the weak pairing
needs. -/
theorem integrableOn_vecNormSq_of_sEnergyOn_ne_top_restrict {b : CoeffField d}
    {V : Set (Vec d)} {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume.restrict V, IsEllipticMatrix lam Lam (b x))
    {F : Vec d → Vec d}
    (hF : ∀ j, AEStronglyMeasurable (fun x => F x j) (volume.restrict V))
    (hfin : sEnergyOn b V F ≠ ⊤) :
    IntegrableOn (fun x => vecNormSq (F x)) V volume :=
  (integrableOn_vecNormSq_iff_lintegral_ne_top hF).2
    ((sEnergyOn_ne_top_iff_restrict (Lam := Lam) hlam hell F).1 hfin)

/-- **Finite weighted energy forces `F ∈ L²(V)`**, which is the hypothesis the
absolute convergence of the weak pairing needs. -/
theorem integrableOn_vecNormSq_of_sEnergyOn_ne_top {b : CoeffField d}
    {V : Set (Vec d)} {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x)) {F : Vec d → Vec d}
    (hF : ∀ j, AEStronglyMeasurable (fun x => F x j) (volume.restrict V))
    (hfin : sEnergyOn b V F ≠ ⊤) :
    IntegrableOn (fun x => vecNormSq (F x)) V volume :=
  integrableOn_vecNormSq_of_sEnergyOn_ne_top_restrict (Lam := Lam) hlam
    (ae_restrict_of_ae hell) hF hfin

end

end HighContrast
end HCPolySupport
