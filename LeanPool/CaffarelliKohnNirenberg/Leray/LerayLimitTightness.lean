/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Leray Limit Tightness

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace CKN.Leray

/-- Local `L²` convergence becomes global when the discarded part is uniformly
small for the sequence and its limit. -/
theorem lerayLimit_eLpNorm_tendsto_of_local_and_uniform_tails
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α}
    (F : ℕ → α → E) (G : α → E) (K : ℕ → Set α)
    (hK : ∀ m, MeasurableSet (K m))
    (hlocal : ∀ m, Tendsto
      (fun n => eLpNorm (F n - G) 2 (μ.restrict (K m))) atTop (𝓝 0))
    (hFtail : ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ m : ℕ in atTop,
      ∀ n, eLpNorm ((K m)ᶜ.indicator (F n)) 2 μ ≤ ε)
    (hGtail : ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ m : ℕ in atTop,
      eLpNorm ((K m)ᶜ.indicator G) 2 μ ≤ ε) :
    Tendsto (fun n => eLpNorm (F n - G) 2 μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hlinear : Tendsto (fun η : ℝ≥0∞ => η + η + η) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun η : ℝ≥0∞ => η + η + η) := by fun_prop
    have hcont0 : ContinuousAt (fun η : ℝ≥0∞ => η + η + η) 0 :=
      hcont.continuousAt
    simpa only [zero_add] using hcont0.tendsto
  have hev : ∀ᶠ η : ℝ≥0∞ in 𝓝 0, η + η + η < ε :=
    hlinear.eventually (gt_mem_nhds hε)
  obtain ⟨η, hηpos, hηsmall⟩ := ENNReal.nhds_zero_basis_Iic.eventually_iff.mp hev
  have hηε : η + η + η < ε := hηsmall (Set.mem_Iic.mpr le_rfl)
  obtain ⟨mF, hmF⟩ := Filter.eventually_atTop.mp (hFtail η hηpos)
  obtain ⟨mG, hmG⟩ := Filter.eventually_atTop.mp (hGtail η hηpos)
  let m := max mF mG
  have hmFn (n : ℕ) : eLpNorm ((K m)ᶜ.indicator (F n)) 2 μ ≤ η :=
    hmF m (le_max_left _ _) n
  have hmGn : eLpNorm ((K m)ᶜ.indicator G) 2 μ ≤ η :=
    hmG m (le_max_right _ _)
  have hN : ∀ᶠ n : ℕ in atTop,
      eLpNorm (F n - G) 2 (μ.restrict (K m)) ≤ η :=
    (ENNReal.tendsto_nhds_zero.mp (hlocal m)) η hηpos
  filter_upwards [hN] with n hn
  have hlocaln : eLpNorm (K m |>.indicator (F n - G)) 2 μ ≤ η := by
    calc
      eLpNorm ((K m).indicator (F n - G)) 2 μ =
          eLpNorm (F n - G) 2 (μ.restrict (K m)) :=
        eLpNorm_indicator_eq_eLpNorm_restrict (p := 2) (μ := μ)
          (f := F n - G) (s := K m) (hK m)
      _ ≤ η := hn
  have htailSubFun : ((K m)ᶜ).indicator (F n - G) =
      ((K m)ᶜ).indicator (F n) - ((K m)ᶜ).indicator G := by
    funext x
    by_cases hx : x ∈ (K m)ᶜ <;> simp [hx]
  have htailSub : eLpNorm (((K m)ᶜ).indicator (F n - G)) 2 μ ≤ η + η := by
    rw [htailSubFun]
    calc
      eLpNorm (((K m)ᶜ).indicator (F n) - ((K m)ᶜ).indicator G) 2 μ ≤
          eLpNorm (((K m)ᶜ).indicator (F n)) 2 μ +
            eLpNorm (((K m)ᶜ).indicator G) 2 μ :=
        eLpNorm_sub_le (p := 2) (μ := μ)
          (f := ((K m)ᶜ).indicator (F n))
          (g := ((K m)ᶜ).indicator G) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      _ ≤ η + η := add_le_add (hmFn n) hmGn
  have hsplit : F n - G =
      (K m).indicator (F n - G) + ((K m)ᶜ).indicator (F n - G) := by
    funext x
    by_cases hx : x ∈ K m <;> simp [hx]
  calc
    eLpNorm (F n - G) 2 μ ≤
        eLpNorm ((K m).indicator (F n - G)) 2 μ +
          eLpNorm (((K m)ᶜ).indicator (F n - G)) 2 μ := by
      calc
        eLpNorm (F n - G) 2 μ =
            eLpNorm ((K m).indicator (F n - G) +
              ((K m)ᶜ).indicator (F n - G)) 2 μ :=
          congrArg (fun f : α → E => eLpNorm f 2 μ) hsplit
        _ ≤ eLpNorm ((K m).indicator (F n - G)) 2 μ +
            eLpNorm (((K m)ᶜ).indicator (F n - G)) 2 μ :=
          eLpNorm_add_le (p := 2) (μ := μ)
            (f := (K m).indicator (F n - G))
            (g := ((K m)ᶜ).indicator (F n - G))
            (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    _ ≤ η + (η + η) := by exact add_le_add hlocaln htailSub
    _ ≤ ε := le_of_lt (by simpa only [add_assoc] using hηε)

end CKN.Leray

end
