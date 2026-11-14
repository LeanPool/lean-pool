/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Dirichlet

/-!
# HolderGauge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Hölder seminorm and supremum norm

Section 5 measures its forcing fields and its solutions in two gauges: the
supremum norm `‖·‖_{L^∞(y+□_n)}` and the `1/2`-Hölder seminorm
`[·]_{C^{0,1/2}(y+□_n)}`.  Both are stated here as `ℝ≥0∞`-valued quantities, so
that an unbounded family has the value `⊤` rather than silently collapsing, and
both are stated for maps into an arbitrary normed group `E`, so that the scalar
case (a solution `u`) and the vector case (a forcing field `g : Vec d → Vec d`)
are one declaration. The basic lemmas below identify bounds on these
extended-real suprema with pointwise real inequalities.

## References

* ABK26, the function-space conventions and the localized estimates of
  Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport
open scoped ENNReal

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E]

/-! ## 1. The two gauges -/

/-- **`[f]_{C^{0,α}(U)}`**, the `α`-Hölder seminorm of `f` on `U`, as an element
of `ℝ≥0∞`: the supremum of the difference quotients `‖f x - f z‖ / ‖x - z‖^α`
over distinct pairs of points of `U`.  The value is `⊤` exactly when the family
of quotients is unbounded. -/
noncomputable def holderSeminormOn (U : Set (Vec d)) (alpha : ℝ) (f : Vec d → E) : ℝ≥0∞ :=
  ⨆ x ∈ U, ⨆ z ∈ U, ⨆ _ : x ≠ z, ENNReal.ofReal (‖f x - f z‖ / ‖x - z‖ ^ alpha)

/-- **`‖f‖_{L^∞(U)}`** read pointwise: the supremum of `‖f x‖` over `x ∈ U`, as
an element of `ℝ≥0∞`.  This is the pointwise supremum, not the essential
supremum; Section 5 applies it to a continuous representative, for which the two
agree on an open set. -/
noncomputable def supNormOn (U : Set (Vec d)) (f : Vec d → E) : ℝ≥0∞ :=
  ⨆ x ∈ U, ENNReal.ofReal ‖f x‖

theorem supNormOn_le_iff {U : Set (Vec d)} {f : Vec d → E} {c : ℝ≥0∞} :
    supNormOn U f ≤ c ↔ ∀ x ∈ U, ENNReal.ofReal ‖f x‖ ≤ c := by
  simp only [supNormOn, iSup_le_iff]

theorem le_supNormOn {U : Set (Vec d)} {f : Vec d → E} {x : Vec d} (hx : x ∈ U) :
    ENNReal.ofReal ‖f x‖ ≤ supNormOn U f :=
  le_iSup_of_le x (le_iSup_of_le hx le_rfl)

/-- The supremum norm is bounded by an explicit constant exactly when the
pointwise bound holds. -/
theorem supNormOn_le_ofReal_iff {U : Set (Vec d)} {K : ℝ} {f : Vec d → E} (hK : 0 ≤ K) :
    supNormOn U f ≤ ENNReal.ofReal K ↔ ∀ x ∈ U, ‖f x‖ ≤ K := by
  rw [supNormOn_le_iff]
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · exact (ENNReal.ofReal_le_ofReal_iff hK).1 (h x hx)
  · exact (ENNReal.ofReal_le_ofReal_iff hK).2 (h x hx)

theorem le_holderSeminormOn {U : Set (Vec d)} {alpha : ℝ} {f : Vec d → E} {x z : Vec d}
    (hx : x ∈ U) (hz : z ∈ U) (hne : x ≠ z) :
    ENNReal.ofReal (‖f x - f z‖ / ‖x - z‖ ^ alpha) ≤ holderSeminormOn U alpha f :=
  le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le z (le_iSup_of_le hz
    (le_iSup_of_le hne le_rfl))))

/-! ## 2. The seminorm bound is the two-point bound -/

private theorem rpow_norm_sub_pos {alpha : ℝ} {x z : Vec d} (hne : x ≠ z) :
    (0 : ℝ) < ‖x - z‖ ^ alpha := by
  refine Real.rpow_pos_of_pos ?_ alpha
  rw [norm_pos_iff]
  exact sub_ne_zero.2 hne

/-- **The bridge between the `ℝ≥0∞` seminorm and the explicit two-point bound.**
No hypothesis on the exponent `alpha` is needed: the diagonal pair contributes
nothing to the supremum, and on the diagonal the two-point bound is automatic
from `0 ≤ K`. -/
theorem holderSeminormOn_le_ofReal_iff {U : Set (Vec d)} {alpha K : ℝ} {f : Vec d → E}
    (hK : 0 ≤ K) :
    holderSeminormOn U alpha f ≤ ENNReal.ofReal K ↔
      Section4.Support.HolderSeminormBoundOn U alpha K f := by
  simp only [holderSeminormOn, iSup_le_iff, Section4.Support.holderSeminormBoundOn_def]
  constructor
  · intro h x hx z hz
    rcases eq_or_ne x z with rfl | hne
    · have hpow : (0 : ℝ) ≤ ‖x - x‖ ^ alpha := Real.rpow_nonneg (norm_nonneg _) alpha
      simpa using mul_nonneg hK hpow
    · have hpos := rpow_norm_sub_pos (alpha := alpha) hne
      have := h x hx z hz hne
      rw [ENNReal.ofReal_le_ofReal_iff hK, div_le_iff₀ hpos] at this
      exact this
  · intro h x hx z hz hne
    have hpos := rpow_norm_sub_pos (alpha := alpha) hne
    rw [ENNReal.ofReal_le_ofReal_iff hK, div_le_iff₀ hpos]
    exact h x hx z hz

end Algsuperdiff.Section5.Support
