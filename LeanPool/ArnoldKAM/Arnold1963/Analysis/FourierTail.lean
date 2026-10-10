/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Analysis.FourierSeries

/-!
Bounds for the omitted Fourier modes, retaining the exponential cutoff factor.
-/

@[expose] public section
noncomputable section
open scoped NNReal
namespace KamProject.Arnold1963

theorem norm_fourierSeries_tail_le_of_decay {n : ℕ} {a : FourierIndex n → ℂ}
    {M ρ δ γ N : ℝ} {σ : ℝ≥0} (hM : 0 ≤ M) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hγ : 0 ≤ γ) (hσ : (σ : ℝ) ≤ ρ - (δ + γ))
    (ha : ∀ k, ‖a k‖ ≤ M * Real.exp (-(indexLength k * ρ))) :
    ‖(∑' k, fourierTermOnStrip a σ k) -
        ∑ k ∈ fourierModes n N, fourierTermOnStrip a σ k‖ ≤
      M * Real.exp (-N * γ) * (4 / δ) ^ n := by
  classical
  let C := M * Real.exp (-N * γ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsum := summable_fourierTerms_of_decay hM (show 0 < δ + γ by linarith) hσ ha
  have ht := (fourierModes n N).hasSum_iff_compl.mp hsum.hasSum
  have hk := summable_exp_indexLength n hδ
  have hk' := hk.subtype (fun k => k ∉ fourierModes n N)
  have hb : ∀ k : {k // k ∉ fourierModes n N},
      ‖fourierTermOnStrip a σ k.val‖ ≤ C * Real.exp (-δ * indexLength k.val) := by
    intro k
    have hN : N ≤ indexLength k.val := not_mem_fourierModes.mp k.property
    calc
      _ ≤ M * Real.exp (-(δ + γ) * indexLength k.val) :=
        norm_fourierTermOnStrip_le_of_decay hM hσ ha k.val
      _ = M * Real.exp (-γ * indexLength k.val) * Real.exp (-δ * indexLength k.val) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ C * Real.exp (-δ * indexLength k.val) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_left _ hM
        apply Real.exp_le_exp.mpr
        nlinarith
  have hbound := ht.norm_le_of_bounded (hk'.hasSum.mul_left C) hb
  apply hbound.trans
  apply mul_le_mul_of_nonneg_left _ hC
  calc
    _ ≤ ∑' k : FourierIndex n, Real.exp (-δ * indexLength k) :=
      hk'.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
        (fun _ _ => (Real.exp_pos _).le) (fun _ => le_rfl) hk
    _ ≤ (4 / δ) ^ n := tsum_exp_indexLength_le n hδ hδ1

end KamProject.Arnold1963
