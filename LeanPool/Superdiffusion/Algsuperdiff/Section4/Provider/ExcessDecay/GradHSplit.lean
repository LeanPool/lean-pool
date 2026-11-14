/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.RecutAtoms
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.FractionalPoincareWindow

/-!
# GradHSplit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `∇h` flat leg: the `L²` norm against the print's window average

## What this file supplies

The paper's norm convention (/14546) reads

```text
  ‖f‖_{B^s(□_j)}  =  [f]_{B^s(□_j)}  +  3^{-js} |(f)_{□_j}| ,
```

so the flat half of the harmonic-approximation display's `∇h` leg is the
**scale-weighted window average**, not the normalized `L²` norm.  The two
readings are *equivalent up to a dimensional constant* on the anchor's own
windows, and this file proves both directions at the frozen carriers.  Write

```text
  W₂ = (z+□_{n+2}) ∩ □_m ,      W₃ = (z+□_{n+3}) ∩ □_m .
```

* `ofReal_norm_volumeAverageVec_windowTwo_le_eLpNorm_windowThree` — the
  **average ≤ norm** direction: `|(f)_{W₂}| ≤ 9^d ‖f‖_{L²(W₃)}`, by the vector
  Jensen inequality on `W₂` and the `RecutAtoms` volume transport `W₂ ↪ W₃`
  (whose ratio bound `|W₃| ≤ 81^d |W₂|` is the anchor's own geometry binder).
* `eLpNorm_windowThree_le_volumeAverageVec_windowTwo_add_gagliardo` — the
  **norm ≤ average + seminorm** direction:
  ```text
    ‖f‖_{L²(W₃)}  ≤  |(f)_{W₂}|  +  C(d)·3^{ns}·[f]_{H^s(W₃)} ,
  ```
  by the proved mean-zero fractional Poincaré inequality on `W₃`
  (`FractionalPoincareWindow`, `s`-uniform constant `2^{d/2}·27·3^{ns}`)
  together with the same Jensen/transport pair used to move the `W₃` mean to
  the `W₂` mean.  The factor `3^{ns}` is exactly the convention's own
  `3^{-js}`: composed with the display's flat weight `3^n` it produces the
  Gagliardo leg's weight `3^{(1+s)n}` on the nose, which is why the split costs
  **no `s`-power** and proves inside the display's existing legs.

The constant is `s`-uniform in both directions: nothing degenerates as `s ↓ 0`
or `s ↑ 1`.

## References

* ABK26, (the `B^s` norm convention); (the display's `∇h` leg).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Vector Jensen on a window -/

/-- **The vector Jensen inequality on a window.**  The window average of a
vector field is at most its normalized `L²` norm — the *lossy* direction of the
equivalence. -/
theorem ofReal_norm_volumeAverageVec_le_eLpNorm_two {W : Set (Vec d)}
    {f : Vec d → Vec d} (h0 : volume W ≠ 0) (htop : volume W ≠ ⊤)
    (hf : Integrable f (volume.restrict W)) :
    ENNReal.ofReal ‖volumeAverageVec W f‖ ≤
      eLpNorm f 2 (normalizedVolumeMeasureOn W) := by
  have hprob : IsProbabilityMeasure (normalizedVolumeMeasureOn W) :=
    isProbabilityMeasure_normalizedVolumeMeasureOn h0 htop
  have hint : Integrable f (normalizedVolumeMeasureOn W) := by
    rw [normalizedVolumeMeasureOn_def]
    exact hf.smul_measure (ENNReal.inv_ne_top.mpr h0)
  have hav : volumeAverageVec W f = ∫ y, f y ∂(normalizedVolumeMeasureOn W) :=
    (Regularity.integral_normalizedVolumeMeasureOn_eq_volumeAverageVec hf).symm
  rw [hav, ofReal_norm]
  calc ‖∫ y, f y ∂(normalizedVolumeMeasureOn W)‖ₑ
      ≤ ∫⁻ y, ‖f y‖ₑ ∂(normalizedVolumeMeasureOn W) := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm f 1 (normalizedVolumeMeasureOn W) :=
        (eLpNorm_one_eq_lintegral_enorm hint.aestronglyMeasurable).symm
    _ ≤ eLpNorm f 2 (normalizedVolumeMeasureOn W) :=
        eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)

/-- The window average commutes with subtracting a constant. -/
theorem volumeAverageVec_sub_const {W : Set (Vec d)} {f : Vec d → Vec d} (c : Vec d)
    (h0 : volume W ≠ 0) (htop : volume W ≠ ⊤)
    (hf : Integrable f (volume.restrict W)) :
    volumeAverageVec W (fun y => f y - c) = volumeAverageVec W f - c := by
  have hprob : IsProbabilityMeasure (normalizedVolumeMeasureOn W) :=
    isProbabilityMeasure_normalizedVolumeMeasureOn h0 htop
  have hfin : IsFiniteMeasure (volume.restrict W) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr htop⟩
  have hint : Integrable f (normalizedVolumeMeasureOn W) := by
    rw [normalizedVolumeMeasureOn_def]
    exact hf.smul_measure (ENNReal.inv_ne_top.mpr h0)
  have hfc : Integrable (fun y => f y - c) (volume.restrict W) := hf.sub (integrable_const c)
  rw [← Regularity.integral_normalizedVolumeMeasureOn_eq_volumeAverageVec hfc,
    ← Regularity.integral_normalizedVolumeMeasureOn_eq_volumeAverageVec hf,
    integral_sub hint (integrable_const c), integral_const]
  simp

/-! ## 2. The two anchor windows -/

/-- `W₂ ⊆ W₃`: the `n+2` window sits inside the `n+3` one. -/
theorem anchorWindow_two_subset_three (n m : ℤ) (z : Vec d) :
    (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
        openCubeSet (originCube d m)) ⊆
      (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)) := by
  intro p hp
  refine ⟨?_, hp.2⟩
  obtain ⟨q, hq, hqp⟩ := hp.1
  exact ⟨q, openCubeSet_originCube_subset_of_le (by omega) hq, hqp⟩

/-- The `L²` transport `W₂ ↪ W₃` at the dimensional constant `9^d`. -/
theorem eLpNorm_windowTwo_le_windowThree {n m : ℤ} {x z : Vec d}
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
    (f : Vec d → Vec d) :
    eLpNorm f 2 (normalizedVolumeMeasureOn
        (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
          openCubeSet (originCube d m))) ≤
      ENNReal.ofReal ((9 : ℝ) ^ d) *
        eLpNorm f 2 (normalizedVolumeMeasureOn
          (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m))) := by
  have hbase := eLpNorm_le_of_volume_le (E := Vec d) (K := ENNReal.ofReal ((81 : ℝ) ^ d))
    (anchorWindow_two_subset_three n m z) (by simp) (by simp)
    (volume_anchorWindow_le hgeom) f
  have hhalf : (ENNReal.ofReal ((81 : ℝ) ^ d)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal ((9 : ℝ) ^ d) := by
    have h81 : (81 : ℝ) ^ d = ((9 : ℝ) ^ d) ^ (2 : ℕ) := by
      rw [show (81 : ℝ) = 9 ^ (2 : ℕ) by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [ENNReal.ofReal_rpow_of_pos (by positivity : (0 : ℝ) < (81 : ℝ) ^ d), h81,
      ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
  rwa [hhalf] at hbase

/-- **The average ≤ norm direction.**  The `W₂` window average of `f` is at most
`9^d` times its normalized `L²` norm on `W₃` — vector Jensen composed with the
window transport. -/
theorem ofReal_norm_volumeAverageVec_windowTwo_le_eLpNorm_windowThree
    {n m : ℤ} {x z : Vec d} {f : Vec d → Vec d}
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
    (hf : Integrable f (volume.restrict
      (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))) :
    ENNReal.ofReal ‖volumeAverageVec
        (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
          openCubeSet (originCube d m)) f‖ ≤
      ENNReal.ofReal ((9 : ℝ) ^ d) *
        eLpNorm f 2 (normalizedVolumeMeasureOn
          (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m))) := by
  have hf2 : Integrable f (volume.restrict
      (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
        openCubeSet (originCube d m))) :=
    hf.mono_measure (Measure.restrict_mono (anchorWindow_two_subset_three n m z) le_rfl)
  refine le_trans (ofReal_norm_volumeAverageVec_le_eLpNorm_two
    (volume_anchorWindowInner_ne_zero hgeom) (volume_anchorWindow_ne_top (n + 2) m z) hf2) ?_
  exact eLpNorm_windowTwo_le_windowThree hgeom f

/-! ## 3. The norm ≤ average + seminorm direction -/

/-- The dimensional, `s`-uniform constant of the split. -/
def gradHSplitConst (d : ℕ) : ℝ := (1 + (9 : ℝ) ^ d) * (2 : ℝ) ^ ((d : ℝ) / 2) * 27

theorem gradHSplitConst_pos (d : ℕ) : 0 < gradHSplitConst d := by
  have h9 : (0 : ℝ) < (9 : ℝ) ^ d := pow_pos (by norm_num) d
  have h2 : (0 : ℝ) < (2 : ℝ) ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hA : (0 : ℝ) < (1 + (9 : ℝ) ^ d) * (2 : ℝ) ^ ((d : ℝ) / 2) :=
    mul_pos (by linarith only [h9]) h2
  exact mul_pos hA (by norm_num)

/-- **The norm ≤ average + seminorm direction.**

```text
  ‖f‖_{L²(W₃)}  ≤  |(f)_{W₂}|  +  gradHSplitConst d · 3^{ns} · [f]_{H^s(W₃)} .
```

The `3^{ns}` is the paper's own `3^{-js}` weight read at `j = n`: composed
with the display's flat weight `3^n` it is exactly the Gagliardo leg's
`3^{(1+s)n}`, so the split consumes **no** `s`-power. -/
theorem eLpNorm_windowThree_le_volumeAverageVec_windowTwo_add_gagliardo
    {n m : ℤ} {x z : Vec d} {s : ℝ} {f : Vec d → Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) (hnm : n + 3 ≤ m)
    (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
    (hf : Integrable f (volume.restrict
      (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)))) :
    eLpNorm f 2 (normalizedVolumeMeasureOn
        (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
          openCubeSet (originCube d m))) ≤
      ENNReal.ofReal ‖volumeAverageVec
          (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
            openCubeSet (originCube d m)) f‖ +
        ENNReal.ofReal (gradHSplitConst d * Real.rpow (3 : ℝ) ((n : ℝ) * s)) *
          normalizedGagliardoESeminormOn
            (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m)) s f := by
  classical
  set W3 : Set (Vec d) :=
    (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m)) with hW3
  set W2 : Set (Vec d) :=
    (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
      openCubeSet (originCube d m)) with hW2
  have hW3ne : volume W3 ≠ 0 := by
    intro h0
    exact volume_anchorWindowInner_ne_zero hgeom
      (le_antisymm (h0 ▸ measure_mono (anchorWindow_two_subset_three n m z)) zero_le)
  have hW3top : volume W3 ≠ ⊤ := volume_anchorWindow_ne_top (n + 3) m z
  have hprob : IsProbabilityMeasure (normalizedVolumeMeasureOn W3) :=
    isProbabilityMeasure_normalizedVolumeMeasureOn hW3ne hW3top
  set c : Vec d := volumeAverageVec W3 f with hc
  set P : ℝ≥0∞ := normalizedGagliardoESeminormOn W3 s f with hP
  -- the proved Poincaré inequality on `W₃`
  have hWeq : truncatedWindow z m (n + 3) = W3 := rfl
  have hpoin : eLpNorm (fun y => f y - c) 2 (normalizedVolumeMeasureOn W3) ≤
      ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) / 2) *
        (3 : ℝ) ^ (((n + 3 : ℤ) : ℝ) * s)) * P := by
    have h := Regularity.eLpNorm_sub_volumeAverageVec_truncatedWindow_le
      (x := z) (m := m) (k := n + 3) (s := s) (f := f) hz hnm hs (by rw [hWeq]; exact hf)
    rw [hWeq] at h
    exact h
  -- the mean move `W₃ → W₂`
  have hfc : Integrable (fun y => f y - c) (volume.restrict W3) := by
    have hfin : IsFiniteMeasure (volume.restrict W3) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hW3top⟩
    exact hf.sub (integrable_const c)
  have hmove : ENNReal.ofReal ‖volumeAverageVec W2 f - c‖ ≤
      ENNReal.ofReal ((9 : ℝ) ^ d) *
        eLpNorm (fun y => f y - c) 2 (normalizedVolumeMeasureOn W3) := by
    have hsub : volumeAverageVec W2 (fun y => f y - c) = volumeAverageVec W2 f - c :=
      volumeAverageVec_sub_const c (volume_anchorWindowInner_ne_zero hgeom)
        (volume_anchorWindow_ne_top (n + 2) m z)
        (hf.mono_measure (Measure.restrict_mono (anchorWindow_two_subset_three n m z) le_rfl))
    have h := ofReal_norm_volumeAverageVec_windowTwo_le_eLpNorm_windowThree
      (n := n) (m := m) (x := x) (z := z) (f := fun y => f y - c) hgeom hfc
    rwa [hsub] at h
  -- the constant leg
  have hconst : eLpNorm (fun _ : Vec d => c) 2 (normalizedVolumeMeasureOn W3) =
      ENNReal.ofReal ‖c‖ := by
    rw [eLpNorm_const _ (by norm_num)
      (IsProbabilityMeasure.ne_zero (normalizedVolumeMeasureOn W3)), measure_univ,
      ENNReal.one_rpow, mul_one, ofReal_norm]
  -- the triangle inequality `f = (f - c) + c`
  have hintc : Integrable (fun y => f y - c) (normalizedVolumeMeasureOn W3) := by
    rw [normalizedVolumeMeasureOn_def]
    exact hfc.smul_measure (ENNReal.inv_ne_top.mpr hW3ne)
  have hsplit : eLpNorm f 2 (normalizedVolumeMeasureOn W3) ≤
      eLpNorm (fun y => f y - c) 2 (normalizedVolumeMeasureOn W3) + ENNReal.ofReal ‖c‖ := by
    have hid : f = fun y => (f y - c) + c := by funext y; abel
    have h := eLpNorm_add_le (μ := normalizedVolumeMeasureOn W3) (p := 2)
      (f := fun y => f y - c) (g := fun _ : Vec d => c) (by norm_num)
    rw [← hconst]
    calc eLpNorm f 2 (normalizedVolumeMeasureOn W3)
        = eLpNorm (fun y => (f y - c) + c) 2 (normalizedVolumeMeasureOn W3) := by rw [← hid]
      _ ≤ _ := h
  -- `‖c‖ ≤ ‖(f)_{W₂}‖ + ‖(f)_{W₂} - c‖`
  have hnormc : ENNReal.ofReal ‖c‖ ≤
      ENNReal.ofReal ‖volumeAverageVec W2 f‖ + ENNReal.ofReal ‖volumeAverageVec W2 f - c‖ := by
    rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hid : volumeAverageVec W2 f - (volumeAverageVec W2 f - c) = c := by abel
    have htri := norm_sub_le (volumeAverageVec W2 f) (volumeAverageVec W2 f - c)
    rw [hid] at htri
    exact htri
  -- assemble
  have hchain : eLpNorm f 2 (normalizedVolumeMeasureOn W3) ≤
      ENNReal.ofReal ‖volumeAverageVec W2 f‖ +
        (1 + ENNReal.ofReal ((9 : ℝ) ^ d)) *
          eLpNorm (fun y => f y - c) 2 (normalizedVolumeMeasureOn W3) := by
    refine hsplit.trans ?_
    have h1 : eLpNorm (fun y => f y - c) 2 (normalizedVolumeMeasureOn W3) +
        ENNReal.ofReal ‖c‖ ≤
        eLpNorm (fun y => f y - c) 2 (normalizedVolumeMeasureOn W3) +
          (ENNReal.ofReal ‖volumeAverageVec W2 f‖ +
            ENNReal.ofReal ((9 : ℝ) ^ d) *
              eLpNorm (fun y => f y - c) 2 (normalizedVolumeMeasureOn W3)) :=
      add_le_add le_rfl (hnormc.trans (add_le_add le_rfl hmove))
    refine h1.trans (le_of_eq ?_)
    ring
  -- the numeric envelope
  have h33 : (3 : ℝ) ^ (((n + 3 : ℤ) : ℝ) * s) ≤ 27 * (3 : ℝ) ^ ((n : ℝ) * s) := by
    have hsplit3 : (3 : ℝ) ^ (((n + 3 : ℤ) : ℝ) * s) =
        (3 : ℝ) ^ ((n : ℝ) * s) * (3 : ℝ) ^ (3 * s) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      push_cast
      ring
    have h27 : (3 : ℝ) ^ (3 * s) ≤ 27 := by
      have hle : (3 : ℝ) ^ (3 * s) ≤ (3 : ℝ) ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hs1])
      have h3 : (3 : ℝ) ^ (3 : ℝ) = 27 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        norm_num
      linarith only [hle, h3]
    have hbase : (0 : ℝ) ≤ (3 : ℝ) ^ ((n : ℝ) * s) := Real.rpow_nonneg (by norm_num) _
    have hstep := mul_le_mul_of_nonneg_left h27 hbase
    rw [hsplit3]
    linarith only [hstep]
  have h9d : (0 : ℝ) ≤ (9 : ℝ) ^ d := le_of_lt (pow_pos (by norm_num) d)
  have h2d : (0 : ℝ) ≤ (2 : ℝ) ^ ((d : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hpos : (0 : ℝ) ≤ (1 + (9 : ℝ) ^ d) * (2 : ℝ) ^ ((d : ℝ) / 2) :=
    mul_nonneg (by linarith only [h9d]) h2d
  have hcoef : (1 + ENNReal.ofReal ((9 : ℝ) ^ d)) *
      ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) / 2) * (3 : ℝ) ^ (((n + 3 : ℤ) : ℝ) * s)) ≤
      ENNReal.ofReal (gradHSplitConst d * Real.rpow (3 : ℝ) ((n : ℝ) * s)) := by
    have hone : (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) := by simp
    have hmulnn : (0 : ℝ) ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * (3 : ℝ) ^ (((n + 3 : ℤ) : ℝ) * s) :=
      mul_nonneg h2d (Real.rpow_nonneg (by norm_num) _)
    rw [hone, ← ENNReal.ofReal_add (by norm_num) h9d,
      ← ENNReal.ofReal_mul (by linarith only [h9d])]
    refine ENNReal.ofReal_le_ofReal ?_
    have hstep := mul_le_mul_of_nonneg_left h33 hpos
    have hrw : Real.rpow (3 : ℝ) ((n : ℝ) * s) = (3 : ℝ) ^ ((n : ℝ) * s) := rfl
    rw [gradHSplitConst, hrw]
    linarith only [hstep, hmulnn]
  refine hchain.trans (add_le_add le_rfl ?_)
  refine le_trans (mul_le_mul_right hpoin _) ?_
  rw [← mul_assoc]
  exact mul_le_mul_left hcoef P

end

end Algsuperdiff.Section4.Provider.ExcessDecay
