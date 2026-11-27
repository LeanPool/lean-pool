/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.Agazzi.Corollary2.Quasiconvexity
public import LeanPool.IwaniecBeurlingAhlfors.CalculusOfVariations.Quasiconvex.Periodic

/-!
# Theorem 1 and Corollary 2 as quasiconvexity in the sense of `CalculusOfVariations`

The paper's Theorem 1 and Corollary 2 test quasiconvexity with `C^∞` periodic maps on the torus.
The package `CalculusOfVariations` defines quasiconvexity (`CalculusOfVariations.Quasiconvex`) with
Lipschitz test maps vanishing outside the unit cube. The two notions agree for Borel, locally
bounded integrands (`CalculusOfVariations.quasiconvexAtOn_iff_periodic`, Dacorogna, Prop. 5.13), and
the paper's proofs give the periodic inequalities for Lipschitz periodic maps
(`theorem1_lipschitz`, `corollary2_lipschitz`). Hence:

* `quasiconvex_integrandL`: `L` is quasiconvex;
* `quasiconvex_burkholderB`: `B_p` is quasiconvex for every `1 < p < ∞`;
* `quasiconvex_burkholder`: for `1 < p < 2`, the Burkholder function
  `(|a₊| − (p − 1)|a₋|)(|a₊| + |a₋|)^{p−1}` (a positive multiple of `B_p`, and quasiconvexity
  passes to positive multiples, `quasiconvex_const_mul`) is quasiconvex.
-/

@[expose] public section

noncomputable section

namespace Agazzi

open MeasureTheory CalculusOfVariations

/-- A continuous `f` that satisfies the periodic inequality `∫_Q [f (A + Dφ) − f (A)] dx ≥ 0` for
all Lipschitz periodic `φ` is quasiconvex: `quasiconvexAtOn_iff_periodic` and `|Q| = 1`. -/
private theorem quasiconvex_of_periodic {f : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hf : Continuous f)
    (h : ∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (φ : (Fin 2 → ℝ) → Fin 2 → ℝ) (C : NNReal),
      LipschitzWith C φ → IsPeriodic φ →
        0 ≤ ∫ x in unitSquare, (f (A + jacobian φ x) - f A)) :
    Quasiconvex f := by
  intro A
  rw [quasiconvexAtOn_iff_periodic hf.measurable (isLocallyBounded_of_continuous hf)]
  intro φ K hφ hper hint
  have h0 : 0 ≤ ∫ x in unitCube 2, (f (A + grad φ x) - f A) := h A φ K hφ hper
  have hvol : volume (unitCube 2) = 1 := rd_volume_unitCube 2
  rw [integral_sub hint (integrableOn_const (by simp [hvol])), setIntegral_const,
    Measure.real, hvol, ENNReal.toReal_one, one_smul] at h0
  linarith

/-- Quasiconvexity is preserved by multiplication by a positive constant (directly from the
definition). -/
theorem quasiconvex_const_mul {f : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hf : Quasiconvex f) {c : ℝ}
    (hc : 0 < c) : Quasiconvex fun A => c * f A := by
  intro A φ K hφ h0 hint
  have hint' : IntegrableOn (fun x => f (A + grad φ x)) (unitCube 2) :=
    (integrable_const_mul_iff (IsUnit.mk0 c hc.ne') _).1 hint
  have := hf A φ K hφ h0 hint'
  rw [integral_const_mul]
  calc (volume (unitCube 2)).toReal * (c * f A) = c * ((volume (unitCube 2)).toReal * f A) := by
        ring
    _ ≤ c * ∫ x in unitCube 2, f (A + grad φ x) := mul_le_mul_of_nonneg_left this hc.le

/-- `L` is quasiconvex, in the sense of `CalculusOfVariations` (Lipschitz test maps vanishing
outside the unit cube): Theorem 1 for Lipschitz periodic maps (`theorem1_lipschitz`) and the
equivalence with periodic test maps (`quasiconvexAtOn_iff_periodic`). -/
theorem quasiconvex_integrandL : CalculusOfVariations.Quasiconvex integrandL :=
  quasiconvex_of_periodic continuous_integrandL fun A _ _ hφ hper => theorem1_lipschitz A hφ hper

/-- `B_p` is quasiconvex for every `1 < p < ∞`, in the sense of `CalculusOfVariations`:
Corollary 2 for Lipschitz periodic maps (`corollary2_lipschitz`) and the equivalence with periodic
test maps (`quasiconvexAtOn_iff_periodic`). -/
theorem quasiconvex_burkholderB {p : ℝ} (hp : 1 < p) :
    CalculusOfVariations.Quasiconvex (burkholderB p) :=
  quasiconvex_of_periodic (continuous_burkholderB hp) fun A _ _ hφ hper =>
    corollary2_lipschitz hp A hφ hper

/-- For `1 < p < 2`, the Burkholder function `(|a₊| − (p − 1)|a₋|)(|a₊| + |a₋|)^{p−1}` is
quasiconvex, in the sense of `CalculusOfVariations`: it is `(p − 1) B_p`
(`burkholderB_of_lt_two`). -/
theorem quasiconvex_burkholder (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    CalculusOfVariations.Quasiconvex fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ (p - 1) *
        (‖conformalPart A‖ - (p - 1) * ‖anticonformalPart A‖) := by
  have hp0 : 0 < p - 1 := by linarith
  have heq : (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      (‖conformalPart A‖ + ‖anticonformalPart A‖) ^ (p - 1) *
        (‖conformalPart A‖ - (p - 1) * ‖anticonformalPart A‖)) =
      fun A => (p - 1) * burkholderB p A := by
    funext A
    rw [burkholderB_of_lt_two hp1 hp2, ← mul_assoc, mul_inv_cancel₀ hp0.ne', one_mul]
  rw [heq]
  exact quasiconvex_const_mul (quasiconvex_burkholderB hp1) hp0

end Agazzi
