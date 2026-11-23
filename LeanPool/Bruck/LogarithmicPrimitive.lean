/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.LogDeriv

/-! # Exponentiating a logarithmic primitive on a connected domain -/

public section

open Set

namespace Bruck

/-- A nonvanishing function with a logarithmic primitive equals a nonzero
multiple of the exponential of the primitive on the open preconnected domain. -/
theorem exists_mul_exp_of_logarithmic_primitive {q P : ℂ → ℂ} {s : Set ℂ}
    (hs : IsOpen s) (hc : IsPreconnected s) (hq : DifferentiableOn ℂ q s)
    (hn : ∀ z ∈ s, q z ≠ 0) (hP : ∀ z ∈ s, HasDerivAt P (deriv q z / q z) z) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z ∈ s, q z = c * Complex.exp (P z) := by
  let e : ℂ → ℂ := fun z => Complex.exp (P z)
  have hde (z : ℂ) (hz : z ∈ s) : HasDerivAt e (e z * (deriv q z / q z)) z :=
    (hP z hz).cexp
  have he : DifferentiableOn ℂ e s :=
    fun z hz => (hde z hz).differentiableAt.differentiableWithinAt
  have hne (z : ℂ) : e z ≠ 0 := Complex.exp_ne_zero (P z)
  apply (logDeriv_eqOn_iff hq he hs hc (fun z _ => hne z) hn).mp
  intro z hz
  rw [logDeriv_apply, logDeriv_apply, (hde z hz).deriv, mul_div_cancel_left₀ _ (hne z)]

end Bruck
