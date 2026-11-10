/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Strict-sublevel continuation

A comparison valid on a strict sublevel propagates a smaller uniform bound
for all finite times. Compactness is applied only to the time interval;
uniform upper continuity controls all spatial points at once.
-/

@[expose] public section

open Set

namespace EhrhardGaussian.Ehrhard

/-- A comparison on a strict sublevel propagates a smaller uniform bound while preserving the strict
gap. -/
theorem strict_sublevel_continuation {α : Type*} {F : ℝ → α → ℝ} {T a b : ℝ}
    (hT : 0 ≤ T) (hba : b < a)
    (hcont : ∀ x, ContinuousOn (fun s => F s x) (Icc 0 T))
    (huniform : ∀ c ∈ Icc 0 T, ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ s ∈ Icc 0 T, |s - c| < η → ∀ x, F s x < F c x + ε)
    (hcompare : ∀ c d : ℝ, c ∈ Icc 0 T → d ∈ Icc 0 T → c ≤ d →
      (∀ s ∈ Icc c d, ∀ x, F s x < a) → (∀ x, F c x ≤ b) → ∀ x, F d x ≤ b)
    (hzero : ∀ x, F 0 x ≤ b) : ∀ x, F T x ≤ b := by
  classical
  let S : Set (Icc (0 : ℝ) T) := {s | ∀ x, F (s : ℝ) x ≤ b}
  have hclosed : IsClosed S := by
    have hi : IsClosed (⋂ x : α, {s : Icc (0 : ℝ) T | F (s : ℝ) x ≤ b}) :=
      isClosed_iInter fun x => isClosed_Iic.preimage (hcont x).domRestrict
    convert hi using 1
    ext s
    simp only [S, mem_ofPred_eq, mem_iInter]
  have hnonempty : S.Nonempty := ⟨⟨0, le_rfl, hT⟩, hzero⟩
  obtain ⟨c, hcS, hcmax⟩ := hclosed.isCompact.exists_isGreatest hnonempty
  change ∀ x, F (c : ℝ) x ≤ b at hcS
  have hcT : (c : ℝ) = T := by
    apply le_antisymm c.property.2
    by_contra hnot
    have hct : (c : ℝ) < T := lt_of_not_ge hnot
    obtain ⟨η, hη, hηbound⟩ := huniform c c.property ((a - b) / 2) (half_pos (sub_pos.mpr hba))
    let d := min T ((c : ℝ) + η / 2)
    have hcd : (c : ℝ) < d := lt_min hct (by linarith only [hη])
    have hd : d ∈ Icc (0 : ℝ) T := ⟨c.property.1.trans hcd.le, min_le_left _ _⟩
    have hstrict : ∀ s ∈ Icc (c : ℝ) d, ∀ x, F s x < a := by
      intro s hs x
      have hsT : s ∈ Icc (0 : ℝ) T := ⟨c.property.1.trans hs.1, hs.2.trans hd.2⟩
      have hdist : |s - (c : ℝ)| < η := by
        rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
        have hsd : s ≤ (c : ℝ) + η / 2 := hs.2.trans (min_le_right _ _)
        linarith only [hsd, hη]
      have h := hηbound s hsT hdist x
      linarith only [h, hcS x, hba]
    have hdS : (⟨d, hd⟩ : Icc (0 : ℝ) T) ∈ S :=
      hcompare c d c.property hd hcd.le hstrict hcS
    have hmax : d ≤ (c : ℝ) := hcmax hdS
    exact (not_le_of_gt hcd) hmax
  simpa only [hcT] using hcS

/-- Uniform Lipschitz continuity supplies both continuity conditions in the
continuation lemma. This version starts at an arbitrary finite time `c`. -/
theorem strict_sublevel_continuation_of_uniform_lipschitz {α : Type*}
    {F : ℝ → α → ℝ} {c T a b C : ℝ} (hcT : c ≤ T) (hba : b < a) (hC : 0 ≤ C)
    (hLip : ∀ s ∈ Icc c T, ∀ t ∈ Icc c T, ∀ x, |F s x - F t x| ≤ C * |s - t|)
    (hcompare : ∀ r s : ℝ, r ∈ Icc c T → s ∈ Icc c T → r ≤ s →
      (∀ t ∈ Icc r s, ∀ x, F t x < a) → (∀ x, F r x ≤ b) → ∀ x, F s x ≤ b)
    (hstart : ∀ x, F c x ≤ b) : ∀ x, F T x ≤ b := by
  let G := fun r x => F (c + r) x
  have hmem (r) (hr : r ∈ Icc (0 : ℝ) (T - c)) : c + r ∈ Icc c T := by
    constructor <;> linarith only [hr.1, hr.2]
  have hshiftLip (r) (hr : r ∈ Icc (0 : ℝ) (T - c))
      (s) (hs : s ∈ Icc (0 : ℝ) (T - c)) (x) : |G r x - G s x| ≤ C * |r - s| := by
    simpa only [G, show c + r - (c + s) = r - s by ring] using hLip _ (hmem r hr) _ (hmem s hs) x
  have hcont (x) : ContinuousOn (fun r => G r x) (Icc 0 (T - c)) := by
    have h : LipschitzOnWith ⟨C, hC⟩ (fun r => G r x) (Icc 0 (T - c)) :=
      LipschitzOnWith.of_dist_le_mul (fun r hr s hs => by
        change |G r x - G s x| ≤ C * |r - s|
        exact hshiftLip r hr s hs x)
    exact h.continuousOn
  have huniform (r) (hr : r ∈ Icc (0 : ℝ) (T - c)) (ε : ℝ) (hε : 0 < ε) :
      ∃ η : ℝ, 0 < η ∧ ∀ s ∈ Icc (0 : ℝ) (T - c), |s - r| < η → ∀ x, G s x < G r x + ε := by
    have hC₁ : 0 < C + 1 := by linarith only [hC]
    refine ⟨ε / (C + 1), div_pos hε hC₁, ?_⟩
    intro s hs hdist x
    have hsmall : C * (ε / (C + 1)) < ε := by
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ hC₁).mpr
      nlinarith only [hε]
    have hmul := mul_le_mul_of_nonneg_left hdist.le hC
    have h := (le_abs_self (G s x - G r x)).trans ((hshiftLip s hs r hr x).trans hmul)
    linarith only [h, hsmall]
  have hcomp (r s : ℝ) (hr : r ∈ Icc (0 : ℝ) (T - c))
      (hs : s ∈ Icc (0 : ℝ) (T - c)) (hrs : r ≤ s)
      (hsub : ∀ t ∈ Icc r s, ∀ x, G t x < a) (hzero : ∀ x, G r x ≤ b) : ∀ x, G s x ≤ b := by
    apply hcompare (c + r) (c + s) (hmem r hr) (hmem s hs) (by linarith only [hrs]) _ hzero
    intro t ht x
    have ht' : t - c ∈ Icc r s := by constructor <;> linarith only [ht.1, ht.2]
    simpa only [G, add_sub_cancel] using hsub (t - c) ht' x
  have h := strict_sublevel_continuation (sub_nonneg.mpr hcT) hba hcont huniform hcomp
    (by simpa only [G, add_zero] using hstart)
  simpa only [G, add_sub_cancel] using h

end EhrhardGaussian.Ehrhard

end
