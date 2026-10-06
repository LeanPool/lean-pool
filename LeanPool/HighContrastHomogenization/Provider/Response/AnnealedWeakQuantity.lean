/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileWeakCarriers

/-!
# High-contrast homogenization: Provider.Response.AnnealedWeakQuantity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The annealed weak quantities as integrals of samplewise majorants

The weak quantities of the profile are squared `L²` norms of samplewise weak
seminorms.  A samplewise estimate for a term of the response split therefore
has to be turned into an estimate for the expectation of that term, and its
samplewise majorant has to be recognized as the integrand whose integral is the
weak quantity.

Both steps are recorded here.  The squared `L²` norm of an extended-nonnegative
observable is the integral of its square, which identifies the weak quantities
with integrals of the squared weak roots; and the expectation of a real
observable is dominated by the integral of its samplewise majorant, which is the
Jensen step.  Nothing about the geometry of the weak seminorm is used.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

noncomputable section

open MeasureTheory

open scoped ENNReal

variable {d : ℕ}

/-! ## The squared norm as an integral -/

/-- The square of the `L²` norm of an extended-nonnegative observable is the
integral of its square. -/
theorem eLpNorm_two_sq_eq_lintegral_sq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (g : α → ℝ≥0∞) (hg : AEStronglyMeasurable g μ) :
    eLpNorm g 2 μ ^ (2 : ℕ) = ∫⁻ a, g a ^ (2 : ℕ) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hg]
  simp only [ENNReal.toReal_ofNat, enorm_eq_self]
  rw [← ENNReal.rpow_natCast (_ ^ (1 / (2 : ℝ))) 2, ← ENNReal.rpow_mul]
  norm_num

/-- The integral of the square of an extended-nonnegative observable is at
most the square of its `L²` norm, with no measurability assumption. -/
private theorem lintegral_sq_le_eLpNorm_two_sq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (g : α → ℝ≥0∞) :
    ∫⁻ a, g a ^ (2 : ℕ) ∂μ ≤ eLpNorm g 2 μ ^ (2 : ℕ) := by
  by_cases hg : AEStronglyMeasurable g μ
  · exact (eLpNorm_two_sq_eq_lintegral_sq μ g hg).ge
  · rw [eLpNorm_of_not_aestronglyMeasurable hg, ENNReal.top_pow two_ne_zero]
    exact le_top

/-- The primal weak quantity is the integral of the squared primal weak
root. -/
theorem profilePrimalWeakQuantity_eq_lintegral (P : Measure (CoeffSpace d))
    (m0 : Mat d) {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (sample : CoeffSpace d → CoeffSpace d) (p r : Vec d)
    (hroot : AEStronglyMeasurable (profilePrimalWeakRoot m0 hq t sample p r
      (profilePrimalCenter P hq t sample p r)) P) :
    profilePrimalWeakQuantity P m0 hq t sample p r =
      ∫⁻ a, profilePrimalWeakRoot m0 hq t sample p r
        (profilePrimalCenter P hq t sample p r) a ^ (2 : ℕ) ∂P := by
  rw [profilePrimalWeakQuantity_eq]
  exact eLpNorm_two_sq_eq_lintegral_sq P _ hroot

/-- The coefficient-transpose weak quantity is the integral of the squared
adjoint weak root. -/
theorem profileAdjointWeakQuantity_eq_lintegral (P : Measure (CoeffSpace d))
    (m0 : Mat d) {q : Mat d} (hq : q.PosDef) (t : ℤ)
    (sample : CoeffSpace d → CoeffSpace d) (p r : Vec d)
    (hroot : AEStronglyMeasurable (profileAdjointWeakRoot m0 hq t sample p r
      (profileAdjointCenter P hq t sample p r)) P) :
    profileAdjointWeakQuantity P m0 hq t sample p r =
      ∫⁻ a, profileAdjointWeakRoot m0 hq t sample p r
        (profileAdjointCenter P hq t sample p r) a ^ (2 : ℕ) ∂P := by
  rw [profileAdjointWeakQuantity_eq]
  exact eLpNorm_two_sq_eq_lintegral_sq P _ hroot

/-! ## The Jensen step -/

/-- **The expectation against a samplewise majorant.**  A samplewise bound by a
constant multiple of an extended-nonnegative majorant bounds the expectation by
the same multiple of the integral of that majorant. -/
theorem ofReal_abs_integral_le_mul_lintegral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} {C : ℝ≥0∞} {g : α → ℝ≥0∞} (hC : C ≠ ⊤)
    (hmajorant : ∀ᵐ a ∂μ, ENNReal.ofReal |f a| ≤ C * g a) :
    ENNReal.ofReal |∫ a, f a ∂μ| ≤ C * ∫⁻ a, g a ∂μ := by
  calc ENNReal.ofReal |∫ a, f a ∂μ|
      = ‖∫ a, f a ∂μ‖ₑ := (Real.enorm_eq_ofReal_abs _).symm
    _ ≤ ∫⁻ a, ‖f a‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ a, C * g a ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hmajorant] with a ha
        rwa [Real.enorm_eq_ofReal_abs]
    _ = C * ∫⁻ a, g a ∂μ := lintegral_const_mul' _ _ hC

/-! ## The weak components -/

/-- **The primal weak component.**  A samplewise bound by a multiple of the
squared primal weak root becomes a bound for the expectation by the same
multiple of the primal weak quantity. -/
theorem ofReal_abs_integral_le_mul_profilePrimalWeakQuantity
    (P : Measure (CoeffSpace d)) (m0 : Mat d) {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (sample : CoeffSpace d → CoeffSpace d) (p r : Vec d)
    {term : CoeffSpace d → ℝ} {Cdiv : ℝ}
    (hmajorant : ∀ᵐ a ∂P, ENNReal.ofReal |term a| ≤
      ENNReal.ofReal Cdiv *
        profilePrimalWeakRoot m0 hq t sample p r
          (profilePrimalCenter P hq t sample p r) a ^ (2 : ℕ)) :
    ENNReal.ofReal |∫ a, term a ∂P| ≤
      ENNReal.ofReal Cdiv * profilePrimalWeakQuantity P m0 hq t sample p r := by
  rw [profilePrimalWeakQuantity_eq]
  exact (ofReal_abs_integral_le_mul_lintegral ENNReal.ofReal_ne_top hmajorant).trans
    (mul_le_mul' le_rfl (lintegral_sq_le_eLpNorm_two_sq P _))

/-- The coefficient-transpose weak component. -/
theorem ofReal_abs_integral_le_mul_profileAdjointWeakQuantity
    (P : Measure (CoeffSpace d)) (m0 : Mat d) {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (sample : CoeffSpace d → CoeffSpace d) (p r : Vec d)
    {term : CoeffSpace d → ℝ} {Cdiv : ℝ}
    (hmajorant : ∀ᵐ a ∂P, ENNReal.ofReal |term a| ≤
      ENNReal.ofReal Cdiv *
        profileAdjointWeakRoot m0 hq t sample p r
          (profileAdjointCenter P hq t sample p r) a ^ (2 : ℕ)) :
    ENNReal.ofReal |∫ a, term a ∂P| ≤
      ENNReal.ofReal Cdiv * profileAdjointWeakQuantity P m0 hq t sample p r := by
  rw [profileAdjointWeakQuantity_eq]
  exact (ofReal_abs_integral_le_mul_lintegral ENNReal.ofReal_ne_top hmajorant).trans
    (mul_le_mul' le_rfl (lintegral_sq_le_eLpNorm_two_sq P _))

/-! ## The two-step form -/

end

end Response
end HighContrast
end HCPolySupport
