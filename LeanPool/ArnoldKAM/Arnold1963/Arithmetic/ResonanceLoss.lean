/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Arithmetic.ResonanceDomain

/-!
The single-step resonance loss combines new shells with erosion layers of existing tubes.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace KamProject.Arnold1963

/-- The dimension-dependent coefficient bounding the measure of resonant shells. -/
def resonanceLossConstant (n : ℕ) : ℝ := n * 2 ^ (n + 2)

theorem resonanceLossConstant_nonneg (n : ℕ) : 0 ≤ resonanceLossConstant n := by
  unfold resonanceLossConstant; positivity

theorem tube_count_budget {n : ℕ} {N : ℝ} (hn : 0 < n) (hN : 1 < N) :
    1 + 2 * n * (lowModes n N).card ≤ resonanceLossConstant n * N ^ n := by
  have hc := card_lowModes_le hn hN
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hNp : 1 ≤ N ^ n := one_le_pow₀ hN.le
  have hB : (1 : ℝ) ≤ n * 2 ^ n * N ^ n := by
    simpa using mul_le_mul (mul_le_mul hnR h2 (by norm_num) (by positivity)) hNp
      (by norm_num) (by positivity : (0 : ℝ) ≤ n * 2 ^ n)
  have hh := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ 2 * n by positivity)
  have he : resonanceLossConstant n * N ^ n = 4 * (n * 2 ^ n * N ^ n) := by
    unfold resonanceLossConstant
    rw [pow_add]
    norm_num
    ring
  rw [he]
  nlinarith

theorem ResonanceDomainState.erosion_loss {n : ℕ} {K N D : ℝ} {Ω : Set (ComplexSpace n)}
    (s : ResonanceDomainState n K N) (h : TypeD Ω D) (hn : 0 < n) (hN : 1 < N) (d : ℝ≥0) :
    realVolume (s.domain Ω \ erosion (s.domain Ω) d) ≤
      ENNReal.ofReal (resonanceLossConstant n * D * (d : ℝ) * N ^ n) * realVolume Ω := by
  have hh := h.finiteTube_erosion_layer (lowModes n N) integerCovector (fun _ => 0)
    s.width s.radius 0 d (by positivity) (fun k hk => (mem_lowModes.mp hk).1) s.width_pos
  simp only [erosion_zero, NNReal.coe_zero, sub_zero] at hh
  apply hh.trans
  apply mul_le_mul' (ENNReal.ofReal_le_ofReal _) le_rfl
  have hc := mul_le_mul_of_nonneg_left (tube_count_budget hn hN)
    (show 0 ≤ D * (d : ℝ) by positivity [h.constant_pos])
  nlinarith [hc]

theorem newShellBudget_nonneg (N₀ N₁ : ℝ) : 0 ≤ newShellBudget N₀ N₁ := by
  exact Finset.sum_nonneg fun _ _ => by positivity

theorem TypeD.ar_loss_le {n : ℕ} {K N₀ N₁ D : ℝ} {Ω : Set (ComplexSpace n)}
    (h : TypeD Ω D) (s : ResonanceDomainState n K N₀)
    (hn : 0 < n) (hK : 0 < K) (hN₀ : 1 ≤ N₀) (hN₁ : 1 < N₁) (hNN : N₀ ≤ N₁)
    (d : ℝ≥0) :
    realVolume (s.domain Ω \ erosion (nonresonantDomain (s.domain Ω) id K N₁) d) ≤
      ENNReal.ofReal (resonanceLossConstant n * D *
        (K * newShellBudget N₀ N₁ + (d : ℝ) * N₁ ^ n)) * realVolume Ω := by
  let E := s.domain Ω
  let F := nonresonantDomain E id K N₁
  have hsub : E \ erosion F d ⊆ (E \ F) ∪ (F \ erosion F d) := by
    intro x hx
    by_cases hf : x ∈ F
    · exact Or.inr ⟨hf, hx.2⟩
    · exact Or.inl ⟨hx.1, hf⟩
  have hnew := h.new_resonance_loss_le (N₁ := N₁) hn hK.le hN₀
    (s.subset Ω) (fun _ hx => s.nonresonant hx)
  have herode := (s.cut hK hNN).erosion_loss h hn hN₁ d
  rw [s.cut_domain hK hNN Ω] at herode
  have hc : (2 : ℝ) ^ (n + 1) * n ≤ resonanceLossConstant n := by
    simp only [resonanceLossConstant, pow_add, pow_one]
    norm_num
    nlinarith [show (0 : ℝ) ≤ 2 ^ n * n by positivity]
  have hnew' : realVolume (E \ F) ≤
      ENNReal.ofReal (resonanceLossConstant n * D * (K * newShellBudget N₀ N₁)) * realVolume Ω := by
    apply hnew.trans
    apply mul_le_mul' (ENNReal.ofReal_le_ofReal _) le_rfl
    have hh := mul_le_mul_of_nonneg_right hc
      (show 0 ≤ D * K * newShellBudget N₀ N₁ by
        positivity [h.constant_pos, newShellBudget_nonneg N₀ N₁])
    nlinarith [hh]
  calc
    _ ≤ realVolume ((E \ F) ∪ (F \ erosion F d)) := realVolume_mono hsub
    _ ≤ realVolume (E \ F) + realVolume (F \ erosion F d) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (resonanceLossConstant n * D * (K * newShellBudget N₀ N₁)) * realVolume Ω +
        ENNReal.ofReal (resonanceLossConstant n * D * (d : ℝ) * N₁ ^ n) * realVolume Ω :=
      add_le_add hnew' herode
    _ = _ := by
      rw [← add_mul, ← ENNReal.ofReal_add
        (by positivity [resonanceLossConstant_nonneg n, h.constant_pos,
          newShellBudget_nonneg N₀ N₁])
        (by positivity [resonanceLossConstant_nonneg n, h.constant_pos, hN₁])]
      have he : resonanceLossConstant n * D * (K * newShellBudget N₀ N₁) +
          resonanceLossConstant n * D * (d : ℝ) * N₁ ^ n =
          resonanceLossConstant n * D * (K * newShellBudget N₀ N₁ + (d : ℝ) * N₁ ^ n) := by ring
      rw [he]

end KamProject.Arnold1963
