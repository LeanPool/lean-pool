/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.GoodTimes
public import LeanPool.EscauriazaSereginSverak.LPS.StrongSolution

/-!
# Endpoint data for strong solutions

The closed-interval strong-solution class supplies an `H¹ ∩ J` endpoint
slice, which can be used as data for a translated local strong solution
(`lem:lps-continuation`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The terminal slice of a strong solution is solenoidal and belongs to
`H¹` with its specified weak gradient (`lem:lps-continuation`). -/
theorem lps_strong_solution_endpoint_trace
    {t₀ t₁ : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ t₁ u Du p) :
    IsLpsGoodTime u Du t₁ ∧
      Tendsto
        (fun s : ℝ => eLpNorm (fun x : Vec3 => u (x, s) - u (x, t₁)) 2 volume)
        (nhdsWithin t₁ (Icc t₀ t₁)) (nhds 0) ∧
      Tendsto
        (fun s : ℝ => eLpNorm (fun x : Vec3 => Du (x, s) - Du (x, t₁)) 2 volume)
        (nhdsWithin t₁ (Icc t₀ t₁)) (nhds 0) := by
  rcases hU with ⟨ht, hSlices, hcont, _hderivs, _hp, _hequation⟩
  have ht₁ : t₁ ∈ Icc t₀ t₁ := ⟨le_of_lt ht, le_rfl⟩
  rcases hcont t₁ ht₁ with ⟨huTrace, hDuTrace⟩
  have hterminal := hSlices t₁ ht₁
  exact ⟨⟨hterminal.2, hterminal.1⟩, huTrace, hDuTrace⟩

/-- The terminal slice of a strong solution is solenoidal and belongs to
`H¹` with its specified weak gradient (`lem:lps-continuation`). -/
theorem lps_strong_solution_endpoint_good_time
    {t₀ t₁ : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ t₁ u Du p) :
    IsLpsGoodTime u Du t₁ :=
  (lps_strong_solution_endpoint_trace hU).1

end ESS
