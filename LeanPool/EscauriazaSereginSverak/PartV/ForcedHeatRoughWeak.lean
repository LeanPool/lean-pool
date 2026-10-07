/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatRoughBounds
public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatSmoothWeak

/-!
# Limit passages for the rough forced heat response

Two convergence mechanisms pass the weak identities of smooth forced heat
responses to the rough response of `lem:pv-stokes`: `L²` convergence against
square-integrable tests, and weighted `L¹` convergence of the responses
against continuous compactly supported tests.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Integrals against a fixed square-integrable function converge along an `L²`
convergent sequence. -/
theorem tendsto_integral_mul_of_eLpNorm_two {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {F ψ : α → ℝ} (hf : ∀ n, MemLp (f n) 2 μ) (hF : MemLp F 2 μ)
    (hψ : MemLp ψ 2 μ) (hlim : Tendsto (fun n => eLpNorm (f n - F) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ a, f n a * ψ a ∂μ) atTop (𝓝 (∫ a, F a * ψ a ∂μ)) := by
  rw [tendsto_iff_edist_tendsto_0]
  have hbound (n : ℕ) : edist (∫ a, f n a * ψ a ∂μ) (∫ a, F a * ψ a ∂μ) ≤
      eLpNorm (f n - F) 2 μ * eLpNorm ψ 2 μ := by
    have hi1 : Integrable (fun a => f n a * ψ a) μ := (hf n).integrable_mul hψ
    have hi2 : Integrable (fun a => F a * ψ a) μ := hF.integrable_mul hψ
    rw [edist_eq_enorm_sub, ← integral_sub hi1 hi2]
    have hpt : (fun a => f n a * ψ a - F a * ψ a) = fun a => (f n - F) a * ψ a := by
      funext a
      simp only [Pi.sub_apply]
      ring
    rw [hpt]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    have hconj : (2 : ℝ).HolderConjugate 2 :=
      (Real.holderConjugate_iff_eq_conjExponent (by norm_num)).2 (by norm_num)
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj
      ((hf n).aestronglyMeasurable.sub hF.aestronglyMeasurable).enorm
      hψ.aestronglyMeasurable.enorm
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        ((hf n).aestronglyMeasurable.sub hF.aestronglyMeasurable),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hψ.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat]
    refine le_of_eq_of_le ?_ h
    congr 1
    funext a
    rw [enorm_mul]
    rfl
  have hzero : Tendsto (fun n => eLpNorm (f n - F) 2 μ * eLpNorm ψ 2 μ) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.mul_const hlim (Or.inr hψ.eLpNorm_lt_top.ne)
    simpa only [zero_mul] using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero
    (fun n => bot_le) hbound

/-- A continuous compactly supported function is dominated by a multiple of the
weight `forcedHeatWeight`. -/
theorem abs_le_mul_forcedHeatWeight {ψ : Vec3 × ℝ → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ z, |ψ z| ≤ c * forcedHeatWeight z.1 := by
  obtain ⟨R, _, hRball⟩ := hψc.isCompact.isBounded.subset_closedBall_lt 0 (0 : Vec3 × ℝ)
  have hBdd : BddAbove (Set.range (fun p : Vec3 × ℝ => ‖ψ p‖)) :=
    hψ.norm.bddAbove_range_of_hasCompactSupport hψc.norm
  let B : ℝ := ⨆ p : Vec3 × ℝ, ‖ψ p‖
  have hB (p : Vec3 × ℝ) : ‖ψ p‖ ≤ B := le_ciSup hBdd p
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨B * (1 + R) ^ 2, by positivity, fun z => ?_⟩
  by_cases hz : ψ z = 0
  · rw [hz, abs_zero]
    exact mul_nonneg (by positivity) (forcedHeatWeight_pos _).le
  · have hmem := hRball (subset_tsupport ψ hz)
    have hnorm : ‖z.1‖ ≤ R := (norm_fst_le z).trans (by
      simpa [Metric.mem_closedBall, dist_zero_right] using hmem)
    have hw : ((1 + R) ^ 2)⁻¹ ≤ forcedHeatWeight z.1 := by
      unfold forcedHeatWeight
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by linarith only [hnorm]) 2
    have hR : 0 ≤ R := (norm_nonneg _).trans hnorm
    calc
      |ψ z| ≤ B := by rw [← Real.norm_eq_abs]; exact hB z
      _ = B * (1 + R) ^ 2 * ((1 + R) ^ 2)⁻¹ := by field_simp
      _ ≤ B * (1 + R) ^ 2 * forcedHeatWeight z.1 :=
        mul_le_mul_of_nonneg_left hw (by positivity)

/-- Integrals of the responses against a continuous compactly supported test
converge on the slab along an `L²` convergent smooth approximation. -/
theorem kernelResponse_integral_tendsto {τ : ℝ} (hτ : 0 < τ)
    {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ} {gn : ℕ → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg2 : ∀ i j, MemLp (g i j) 2 volume)
    (hgsupp : ∀ i j z, g i j z ≠ 0 → 0 < z.2)
    (hgn : ∀ n i j, ContDiff ℝ (⊤ : ℕ∞) (gn n i j))
    (hgnc : ∀ n i j, HasCompactSupport (gn n i j))
    (hgnpos : ∀ n i j, tsupport (gn n i j) ⊆ {p | 0 < p.2})
    (hconv : ∀ i j, Tendsto (fun n => eLpNorm (gn n i j - g i j) 2 volume) atTop (𝓝 0))
    {ψ : Vec3 × ℝ → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (i : Fin 3) :
    Integrable (fun z => kernelResponse g z i * ψ z)
        (volume.restrict ((univ : Set Vec3) ×ˢ Ioo 0 τ)) ∧
    Tendsto (fun n => ∫ z in (univ : Set Vec3) ×ˢ Ioo 0 τ, kernelResponse (gn n) z i * ψ z)
      atTop (𝓝 (∫ z in (univ : Set Vec3) ×ˢ Ioo 0 τ, kernelResponse g z i * ψ z)) := by
  set μ := (volume : Measure (Vec3 × ℝ)).restrict ((univ : Set Vec3) ×ˢ Ioo 0 τ)
  obtain ⟨c, hc0, hcψ⟩ := abs_le_mul_forcedHeatWeight hψ hψc
  have hW := kernelResponse_weighted_tendsto hτ hg2 hgsupp hgn hgnc hgnpos hconv
  have hZnc (n : ℕ) : Continuous (fun z => kernelResponse (gn n) z i) := by
    have h := forcedHeat_contDiff (G := fun i j (z : ParabolicPoint) => gn n i j z)
      (hgn n) (hgnc n) i
    exact h.continuous
  have hZm : AEStronglyMeasurable (fun z => kernelResponse g z i) volume :=
    kernelResponse_component_aestronglyMeasurable (fun i j => (hg2 i j).aestronglyMeasurable) i
  have hint_n (n : ℕ) : Integrable (fun z => kernelResponse (gn n) z i * ψ z) μ :=
    (((hZnc n).mul hψ).integrable_of_hasCompactSupport hψc.mul_left).restrict
  -- pointwise domination of the difference
  have hdiff (n : ℕ) (z : Vec3 × ℝ) :
      ‖(kernelResponse (gn n) z i - kernelResponse g z i) * ψ z‖ₑ ≤
        ENNReal.ofReal c * (ENNReal.ofReal (forcedHeatWeight z.1) *
          ‖kernelResponse (gn n) z - kernelResponse g z‖ₑ) := by
    rw [enorm_mul, Real.enorm_eq_ofReal_abs (ψ z)]
    have h1 : ‖kernelResponse (gn n) z i - kernelResponse g z i‖ₑ ≤
        ‖kernelResponse (gn n) z - kernelResponse g z‖ₑ := by
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (norm_le_pi_norm
        (kernelResponse (gn n) z - kernelResponse g z) i)
    have h2 : ENNReal.ofReal |ψ z| ≤ ENNReal.ofReal c * ENNReal.ofReal (forcedHeatWeight z.1) := by
      rw [← ENNReal.ofReal_mul hc0]
      exact ENNReal.ofReal_le_ofReal (hcψ z)
    calc
      _ ≤ ‖kernelResponse (gn n) z - kernelResponse g z‖ₑ *
          (ENNReal.ofReal c * ENNReal.ofReal (forcedHeatWeight z.1)) := mul_le_mul' h1 h2
      _ = _ := by ring
  have hlint (n : ℕ) : ∫⁻ z, ‖(kernelResponse (gn n) z i - kernelResponse g z i) * ψ z‖ₑ ∂μ ≤
      ENNReal.ofReal c * ∫⁻ z, ENNReal.ofReal (forcedHeatWeight z.1) *
        ‖kernelResponse (gn n) z - kernelResponse g z‖ₑ ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono fun z => hdiff n z
  -- integrability of the rough integrand
  have hW' : ∀ᶠ n in atTop, ∫⁻ z, ENNReal.ofReal (forcedHeatWeight z.1) *
      ‖kernelResponse (gn n) z - kernelResponse g z‖ₑ ∂μ < 1 :=
    hW.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨n0, hn0⟩ := hW'.exists
  have hint : Integrable (fun z => kernelResponse g z i * ψ z) μ := by
    refine ⟨(hZm.mul hψ.aestronglyMeasurable).restrict, ?_⟩
    have hsplit (z : Vec3 × ℝ) : ‖kernelResponse g z i * ψ z‖ₑ ≤
        ‖(kernelResponse (gn n0) z i - kernelResponse g z i) * ψ z‖ₑ +
          ‖kernelResponse (gn n0) z i * ψ z‖ₑ := by
      rw [← enorm_neg ((kernelResponse (gn n0) z i - kernelResponse g z i) * ψ z)]
      refine le_trans (le_of_eq ?_) (enorm_add_le _ _)
      congr 1
      ring
    refine lt_of_le_of_lt (lintegral_mono hsplit) ?_
    rw [lintegral_add_right' _ (hint_n n0).aestronglyMeasurable.enorm]
    refine ENNReal.add_lt_top.2 ⟨?_, (hint_n n0).hasFiniteIntegral⟩
    exact lt_of_le_of_lt (hlint n0) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_trans hn0 ENNReal.one_lt_top))
  refine ⟨hint, ?_⟩
  rw [tendsto_iff_edist_tendsto_0]
  have hbound (n : ℕ) : edist (∫ z, kernelResponse (gn n) z i * ψ z ∂μ)
      (∫ z, kernelResponse g z i * ψ z ∂μ) ≤ ENNReal.ofReal c * ∫⁻ z,
        ENNReal.ofReal (forcedHeatWeight z.1) *
          ‖kernelResponse (gn n) z - kernelResponse g z‖ₑ ∂μ := by
    rw [edist_eq_enorm_sub, ← integral_sub (hint_n n) hint]
    have hpt : (fun z => kernelResponse (gn n) z i * ψ z - kernelResponse g z i * ψ z) =
        fun z => (kernelResponse (gn n) z i - kernelResponse g z i) * ψ z := by
      funext z
      ring
    rw [hpt]
    exact (enorm_integral_le_lintegral_enorm _).trans (hlint n)
  have hzero := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal c) hW
    (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at hzero
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero
    (fun n => bot_le) hbound

end ESS

end
