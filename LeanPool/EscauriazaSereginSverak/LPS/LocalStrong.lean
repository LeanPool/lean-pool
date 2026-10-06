/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.GoodTimes
public import LeanPool.EscauriazaSereginSverak.LPS.StrongSolution
public import LeanPool.EscauriazaSereginSverak.LPS.RegularisedH1Comparison
public import LeanPool.EscauriazaSereginSverak.LPS.RegularisedH1Bounds
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongShift
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegMollifierProfileStandard
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLerayHopfSolution
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongEnergyIdentity
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongHopfBridge
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitSolution

/-!
# Assembly support for the local strong solution

The datum in `prop:lps-local-strong` is given as a good time of its constant
extension. These lemmas transfer that hypothesis to the zero-based
regularized construction and record the finite squared H¹ energy of the
datum.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- A constant-in-time good datum is also a good datum at time zero
(`prop:lps-local-strong`). -/
theorem lps_constant_initial_good_time_at_zero
    {t₀ : ℝ} (b : Vec3 → Vec3) (Db : Vec3 → Fin 3 → Vec3)
    (hGood : ESS.IsLpsGoodTime
      (fun z : ParabolicPoint => b z.1)
      (fun z i => Db z.1 i) t₀) :
    ESS.IsLpsGoodTime
      (fun z : ParabolicPoint => b z.1)
      (fun z i => Db z.1 i) 0 := by
  simpa [ESS.IsLpsGoodTime] using hGood

end ESS.LPS

namespace ESS

/-- `prop:lps-local-strong`: for every solenoidal `H¹` datum there is a strong solution on `[t₀, t₀ + τ]`
with `τ ≥ c (1 + ‖b‖_{H¹})⁻⁴` for an absolute constant `c`, with its initial trace, the energy
equality between any two times, and the Leray--Hopf property. The solution is the limit of the
regularized solutions of `lem:lps-regularized-Hk-start`, translated in time. -/
theorem lps_local_strong :
    ∃ c : ℝ, 0 < c ∧
      ∀ (t₀ : ℝ) (b : Vec3 → Vec3)
        (Db : Vec3 → Fin 3 → Vec3),
        ESS.IsLpsGoodTime
          (fun z : ParabolicPoint => b z.1)
          (fun z i => Db z.1 i) t₀ →
        ∃ τ : ℝ, 0 < τ ∧
          c * Real.rpow
            (1 + Real.sqrt (∫ x : Vec3,
              (∑ i : Fin 3, (b x i) ^ 2) +
                ∑ i : Fin 3, ∑ j : Fin 3, (Db x i j) ^ 2))
            (-4 : ℝ) ≤ τ ∧
          ∃ (u : ParabolicPoint → Vec3)
            (Du : ParabolicPoint → Fin 3 → Vec3)
            (p : ParabolicPoint → ℝ),
            ESS.IsLpsStrongSolution t₀ (t₀ + τ) u Du p ∧
            (fun x : Vec3 => u (x, t₀)) =ᵐ[volume] b ∧
            Tendsto
              (fun s : ℝ =>
                eLpNorm (fun x : Vec3 => u (x, s) - b x) 2 volume)
              (nhdsWithin t₀ (Ioi t₀)) (nhds 0) ∧
            (∀ s t : ℝ, s ∈ Icc t₀ (t₀ + τ) →
              t ∈ Icc t₀ (t₀ + τ) → s ≤ t →
              (∫ x : Vec3, ∑ i : Fin 3, (u (x, t) i) ^ 2) +
                2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo s t),
                  ∑ i : Fin 3, ∑ j : Fin 3, (Du z i j) ^ 2 =
              ∫ x : Vec3, ∑ i : Fin 3, (u (x, s) i) ^ 2) ∧
            CKN.IsLerayHopfSolution τ b
              (fun z : ParabolicPoint => u (z.1, t₀ + z.2))
              (fun z i => Du (z.1, t₀ + z.2) i) := by
  obtain ⟨c, hc, hbounds⟩ := LPS.lps_regularised_uniform_h1_bounds
  refine ⟨c, hc, ?_⟩
  intro t₀ b Db hGood
  have hGood0 := LPS.lps_constant_initial_good_time_at_zero b Db hGood
  obtain ⟨T, M, hT, hcT, hM, hclause⟩ :=
    hbounds CKN.Leray.standardRegMollifierProfile b Db hGood0
  obtain ⟨u₀, Du₀, p₀, hU₀, htrace₀⟩ :=
    LPS.lps_strong_limit_solution CKN.Leray.standardRegMollifierProfile b Db hGood0 T M hT hclause
  have hU := LPS.lps_isLpsStrongSolution_shift (a := t₀) hU₀
  set u : ParabolicPoint → Vec3 := fun z => u₀ (LPS.lpsTimeShift t₀ z) with hu
  set Du : ParabolicPoint → Fin 3 → Vec3 := fun z i => Du₀ (LPS.lpsTimeShift t₀ z) i with hDu
  set p : ParabolicPoint → ℝ := fun z => p₀ (LPS.lpsTimeShift t₀ z) with hp
  have hbJ : CKN.IsInJ b := by simpa using hGood.2
  have hu0 : ∀ x : Vec3, u (x, t₀) = u₀ (x, 0) := fun x => by simp [hu, LPS.lpsTimeShift]
  have htrace : (fun x : Vec3 => u (x, t₀)) =ᵐ[volume] b := by
    simpa only [hu0] using htrace₀
  refine ⟨T, hT, hcT, u, Du, p, hU, htrace, ?_, ?_, ?_⟩
  · have h1 := (hU.2.2.1 t₀ ⟨le_rfl, by linarith only [hT]⟩).1
    have hmem : Icc t₀ (t₀ + T) ∈ nhdsWithin t₀ (Ioi t₀) :=
      mem_of_superset (Ioo_mem_nhdsGT (by linarith only [hT] : t₀ < t₀ + T)) Ioo_subset_Icc_self
    have h2 := h1.mono_left (nhdsWithin_le_of_mem hmem)
    refine h2.congr fun s => ?_
    refine eLpNorm_congr_ae ?_
    filter_upwards [htrace] with x hx
    simp only [hx]
  · obtain ⟨-, -, -, -, -, -, hk⟩ := LPS.lps_unregularised_h1_energy_identity hU
    exact hk
  · have h := lps_strong_solution_is_leray_hopf hU hbJ htrace
    rwa [add_sub_cancel_left] at h

end ESS

end
