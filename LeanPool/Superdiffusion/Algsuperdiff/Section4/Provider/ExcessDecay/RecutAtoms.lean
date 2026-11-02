/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorWindowMove

/-!
# RecutAtoms

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The window move: the three atoms of the re-cut

In the frozen statement's **general** clause five window carriers — the
mean-subtracted `L²` leg's average window and its measure carrier, both
Gagliardo carriers, and the `∇h` `L²` carrier — are read on the *enlarged*
window:

```text
  W  = (z + □_{n+2}) ∩ □_m   is enlarged to   W' = (z + □_{n+3}) ∩ □_m;
```

the in-bracket `3^n |(∇h)_W|` companion deliberately keeps `W`.

Since `W ⊆ W'`, every one of those legs *grows* the window and therefore has to
be paid for at the volume ratio.  This module proves the three atoms:

* `eLpNorm_le_of_volume_le` — the `L²` **carrier move** on nested windows;
* `eLpNorm_sub_volumeAverage_le_two_mul` — the **mean move**: on a normalized
  window the mean-subtracted `L²` norm is within a factor `2` of the norm with
  *any* other constant subtracted (the triangle form of mean optimality; the
  sharp constant `1` is not needed, and the factor is absorbed into the
  existentially quantified `C`);
* `normalizedGagliardoESeminormOn_anchorWindow_le` and
  `eLpNorm_sub_volumeAverage_anchorWindow_le` — the
  two atoms at the anchor's own windows, at the volume ratio `81^d`.

## The volume ratio actually used

The ratio can be priced at `6^d` (from `z ∈ □_m` and `n+2 ≤ m` alone).  The
cheaper route taken here uses the anchor's **own geometry binder**: the child
cube `x + □_n` sits inside `W`, so

```text
  |W'| ≤ |z + □_{n+3}| = 27^d |□_n| ≤ 81^d |x + □_n| ≤ 81^d |W| ,
```

whose square root `9^d` is a perfect power and keeps the arithmetic trivial.  The
frozen statement quantifies `C` existentially, so the constant is immaterial; the
sharper `6^d` is available and unused.

## References

* ABK26, `l.harmonic.approximation.good.scales`; the frozen block of
  `Algsuperdiff/Frozen/Section4/HarmonicApproximation.lean`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E]

/-! ## 1. The measure comparison on nested windows -/

/-- If `B ⊆ A` and `|A| ≤ K |B|` then the normalized measure of `B` is dominated
by `K` times that of `A`. -/
theorem normalizedVolumeMeasureOn_le_smul {A B : Set (Vec d)} {K : ℝ≥0∞}
    (hAB : B ⊆ A) (hK0 : K ≠ 0) (hKtop : K ≠ ⊤)
    (hvol : volume A ≤ K * volume B) :
    Support.normalizedVolumeMeasureOn B ≤ K • Support.normalizedVolumeMeasureOn A := by
  have hinv : (volume B)⁻¹ ≤ K * (volume A)⁻¹ := by
    have h1 : (K * volume B)⁻¹ ≤ (volume A)⁻¹ := ENNReal.inv_le_inv.mpr hvol
    have h2 : K * (K * volume B)⁻¹ = (volume B)⁻¹ := by
      rw [ENNReal.mul_inv (Or.inl hK0) (Or.inl hKtop), ← mul_assoc,
        ENNReal.mul_inv_cancel hK0 hKtop, one_mul]
    calc (volume B)⁻¹ = K * (K * volume B)⁻¹ := h2.symm
      _ ≤ K * (volume A)⁻¹ := mul_le_mul' le_rfl h1
  rw [Support.normalizedVolumeMeasureOn_def, Support.normalizedVolumeMeasureOn_def]
  refine Measure.le_iff'.mpr fun S => ?_
  have hres : (volume.restrict B) S ≤ (volume.restrict A) S :=
    Measure.restrict_mono hAB le_rfl S
  calc ((volume B)⁻¹ • volume.restrict B) S = (volume B)⁻¹ * (volume.restrict B) S := by
        simp only [Measure.smul_apply, smul_eq_mul]
    _ ≤ (K * (volume A)⁻¹) * (volume.restrict A) S := mul_le_mul' hinv hres
    _ = (K • ((volume A)⁻¹ • volume.restrict A)) S := by
        simp only [Measure.smul_apply, smul_eq_mul, mul_assoc]

/-- **The `L²` carrier move.**  If `B ⊆ A` and `|A| ≤ K |B|` then the normalized
`L²` norm over `B` costs `K^{1/2}` against the one over `A`. -/
theorem eLpNorm_le_of_volume_le {A B : Set (Vec d)} {K : ℝ≥0∞}
    (hAB : B ⊆ A) (hK0 : K ≠ 0) (hKtop : K ≠ ⊤)
    (hvol : volume A ≤ K * volume B) (f : Vec d → E) :
    eLpNorm f 2 (Support.normalizedVolumeMeasureOn B) ≤
      K ^ (1 / 2 : ℝ) * eLpNorm f 2 (Support.normalizedVolumeMeasureOn A) := by
  by_cases hf : AEStronglyMeasurable f (Support.normalizedVolumeMeasureOn A)
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hf,
      ENNReal.mul_top (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hK0) hKtop).ne']
    exact le_top
  have hmono : eLpNorm f 2 (Support.normalizedVolumeMeasureOn B) ≤
      eLpNorm f 2 (K • Support.normalizedVolumeMeasureOn A) :=
    eLpNorm_mono_measure _ (normalizedVolumeMeasureOn_le_smul hAB hK0 hKtop hvol)
  have hsmul : eLpNorm f 2 (K • Support.normalizedVolumeMeasureOn A) =
      K ^ (1 / 2 : ℝ) * eLpNorm f 2 (Support.normalizedVolumeMeasureOn A) := by
    rw [eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) f K hf]
    norm_num
  rwa [hsmul] at hmono

/-! ## 2. The normalized window as a probability space -/

/-- A window of positive finite volume carries a probability measure. -/
theorem isProbabilityMeasure_normalizedVolumeMeasureOn {A : Set (Vec d)}
    (h0 : volume A ≠ 0) (htop : volume A ≠ ⊤) :
    IsProbabilityMeasure (Support.normalizedVolumeMeasureOn A) := by
  constructor
  rw [Support.normalizedVolumeMeasureOn_def, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel h0 htop

/-- The Bochner integral against the normalized window measure is CoarseGraining's
`volumeAverage`. -/
theorem integral_normalizedVolumeMeasureOn (A : Set (Vec d)) (f : Vec d → ℝ) :
    ∫ y, f y ∂(Support.normalizedVolumeMeasureOn A) = volumeAverage A f := by
  rw [Support.normalizedVolumeMeasureOn_def, integral_smul_measure, volumeAverage,
    ENNReal.toReal_inv, smul_eq_mul]

/-- `MemLp` transported from the restricted to the normalized window measure. -/
theorem memLp_normalizedVolumeMeasureOn_of_restrict {p : ℝ≥0∞} {A : Set (Vec d)}
    (h0 : volume A ≠ 0) {f : Vec d → E} (h : MemLp f p (volume.restrict A)) :
    MemLp f p (Support.normalizedVolumeMeasureOn A) := by
  rw [Support.normalizedVolumeMeasureOn_def]
  exact h.smul_measure (ENNReal.inv_ne_top.mpr h0)

/-! ## 3. The mean move -/

/-- **The mean move.**  On a normalized window, subtracting the window mean costs
at most a factor `2` against subtracting any other constant.

This is the triangle form of mean optimality: the sharp statement has the
factor `1`, but the frozen theorem's constant is existentially quantified, so
the cheap form suffices. -/
theorem eLpNorm_sub_volumeAverage_le_two_mul {A : Set (Vec d)} (h0 : volume A ≠ 0)
    (htop : volume A ≠ ⊤) {f : Vec d → ℝ}
    (hf : AEStronglyMeasurable f (Support.normalizedVolumeMeasureOn A)) (c : ℝ) :
    eLpNorm (fun y => f y - volumeAverage A f) 2
        (Support.normalizedVolumeMeasureOn A) ≤
      2 * eLpNorm (fun y => f y - c) 2 (Support.normalizedVolumeMeasureOn A) := by
  have := isProbabilityMeasure_normalizedVolumeMeasureOn h0 htop
  set mu : Measure (Vec d) := Support.normalizedVolumeMeasureOn A with hmu
  by_cases hinf : eLpNorm (fun y => f y - c) 2 mu = ⊤
  · rw [hinf, ENNReal.mul_top (by norm_num : (2 : ℝ≥0∞) ≠ 0)]
    exact le_top
  have hgmeas : AEStronglyMeasurable (fun y => f y - c) mu :=
    hf.sub aestronglyMeasurable_const
  have hg : MemLp (fun y => f y - c) 2 mu :=
    (lt_top_iff_ne_top.mpr hinf)
  have hgint : Integrable (fun y => f y - c) mu := hg.integrable (by norm_num)
  have hfint : Integrable f mu := by
    have hsum := hgint.add (integrable_const c)
    refine hsum.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply]
    ring
  have hmean : volumeAverage A f - c = ∫ y, (f y - c) ∂mu := by
    have hfi : ∫ y, f y ∂mu = volumeAverage A f := by
      rw [hmu]
      exact integral_normalizedVolumeMeasureOn A f
    rw [integral_sub hfint (integrable_const c), hfi, integral_const]
    simp
  have hrw : (fun y => f y - volumeAverage A f) =
      fun y => (f y - c) - (∫ y, (f y - c) ∂mu) := by
    funext y
    rw [← hmean]
    ring
  rw [hrw]
  have hconst : eLpNorm (fun _ : Vec d => (∫ y, (f y - c) ∂mu)) 2 mu ≤
      eLpNorm (fun y => f y - c) 2 mu := by
    have hc : eLpNorm (fun _ : Vec d => (∫ y, (f y - c) ∂mu)) 2 mu =
        ‖(∫ y, (f y - c) ∂mu)‖ₑ := by
      rw [eLpNorm_const _ (by norm_num) (IsProbabilityMeasure.ne_zero mu), measure_univ,
        ENNReal.one_rpow, mul_one]
    rw [hc]
    refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
    rw [← eLpNorm_one_eq_lintegral_enorm hgmeas]
    exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  refine le_trans (eLpNorm_sub_le (by norm_num)) ?_
  have hstep : eLpNorm (fun y => f y - c) 2 mu +
      eLpNorm (fun _ : Vec d => (∫ y, (f y - c) ∂mu)) 2 mu ≤
      eLpNorm (fun y => f y - c) 2 mu + eLpNorm (fun y => f y - c) 2 mu :=
    add_le_add le_rfl hconst
  refine le_trans hstep (le_of_eq ?_)
  rw [two_mul]

/-- **The two moves composed.**  On nested windows of comparable volume, the
mean-subtracted normalized `L²` norm over the smaller window is controlled by the
one over the larger, at `2 K^{1/2}`. -/
theorem eLpNorm_sub_volumeAverage_le_of_subset {A B : Set (Vec d)} {K : ℝ≥0∞}
    (hAB : B ⊆ A) (hK0 : K ≠ 0) (hKtop : K ≠ ⊤) (hvol : volume A ≤ K * volume B)
    (hB0 : volume B ≠ 0) (hBtop : volume B ≠ ⊤) {f : Vec d → ℝ}
    (hf : AEStronglyMeasurable f (Support.normalizedVolumeMeasureOn B)) :
    eLpNorm (fun y => f y - volumeAverage B f) 2
        (Support.normalizedVolumeMeasureOn B) ≤
      2 * K ^ (1 / 2 : ℝ) *
        eLpNorm (fun y => f y - volumeAverage A f) 2
          (Support.normalizedVolumeMeasureOn A) := by
  refine le_trans (eLpNorm_sub_volumeAverage_le_two_mul hB0 hBtop hf (volumeAverage A f)) ?_
  have hmove := eLpNorm_le_of_volume_le (E := ℝ) hAB hK0 hKtop hvol
    (fun y => f y - volumeAverage A f)
  calc 2 * eLpNorm (fun y => f y - volumeAverage A f) 2
        (Support.normalizedVolumeMeasureOn B)
      ≤ 2 * (K ^ (1 / 2 : ℝ) * eLpNorm (fun y => f y - volumeAverage A f) 2
          (Support.normalizedVolumeMeasureOn A)) := mul_le_mul' le_rfl hmove
    _ = 2 * K ^ (1 / 2 : ℝ) * eLpNorm (fun y => f y - volumeAverage A f) 2
          (Support.normalizedVolumeMeasureOn A) := by rw [mul_assoc]

/-! ## 4. The atoms at the anchor's own windows -/

/-- The window move's constant: `9^d`, the square root of the volume ratio
`81^d`. -/
def windowMoveConst (d : ℕ) : ℝ := (9 : ℝ) ^ d

theorem windowMoveConst_pos (d : ℕ) : 0 < windowMoveConst d := by
  rw [windowMoveConst]
  positivity

private theorem eightyOne_pow_rpow_half (d : ℕ) :
    ((81 : ℝ) ^ d) ^ (1 / 2 : ℝ) = (9 : ℝ) ^ d := by
  have h81 : (81 : ℝ) ^ d = ((9 : ℝ) ^ d) ^ (2 : ℕ) := by
    rw [show (81 : ℝ) = 9 ^ (2 : ℕ) by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [h81, ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]

private theorem ofReal_eightyOne_pow_rpow_half (d : ℕ) :
    (ENNReal.ofReal ((81 : ℝ) ^ d)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (windowMoveConst d) := by
  rw [ENNReal.ofReal_rpow_of_pos (by positivity : (0 : ℝ) < (81 : ℝ) ^ d),
    windowMoveConst, eightyOne_pow_rpow_half d]

/-- The inner window `W` sits inside the enlarged window `W'`. -/
theorem anchorWindowInner_subset_anchorWindow (n m : ℤ) (z : Vec d) :
    (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
        openCubeSet (originCube d m)) ⊆
      (((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m)) := by
  refine Set.inter_subset_inter_left _ ?_
  rintro p ⟨q, hq, rfl⟩
  exact ⟨q, openCubeSet_originCube_subset_of_le (by omega) hq, rfl⟩

/-- The anchor's child cube sits inside the inner window `W`. -/
theorem child_subset_anchorWindowInner {n m : ℤ} {x z : Vec d}
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m)) :
    (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
        openCubeSet (originCube d m)) := by
  intro p hp
  refine ⟨?_, (hgeom hp).2⟩
  obtain ⟨q, hq, hqp⟩ := (hgeom hp).1
  exact ⟨q, openCubeSet_originCube_subset_of_le (by omega) hq, hqp⟩

/-- The volume of `W'` is at most `81^d` times the volume of `W`. -/
theorem volume_anchorWindow_le {n m : ℤ} {x z : Vec d}
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m)) :
    volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
        openCubeSet (originCube d m))) ≤
      ENNReal.ofReal ((81 : ℝ) ^ d) *
        volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
          openCubeSet (originCube d m))) := by
  have hsplit : ((3 : ℝ) ^ (n + 3)) ^ d ≤ (81 : ℝ) ^ d * ((3 : ℝ) ^ n) ^ d := by
    have hid : ((3 : ℝ) ^ (n + 3)) ^ d = (27 : ℝ) ^ d * ((3 : ℝ) ^ n) ^ d := by
      rw [← mul_pow]
      congr 1
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0) n 3]
      norm_num
      ring
    have hmono : (27 : ℝ) ^ d ≤ (81 : ℝ) ^ d := by
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) d
    have hpos : (0 : ℝ) ≤ ((3 : ℝ) ^ n) ^ d := by positivity
    rw [hid]
    exact mul_le_mul_of_nonneg_right hmono hpos
  have hupper : volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
      openCubeSet (originCube d m))) ≤
      ENNReal.ofReal (((3 : ℝ) ^ (n + 3)) ^ d) := by
    refine le_trans (measure_mono Set.inter_subset_left) ?_
    rw [volume_image_add_openCubeSet z (originCube d (n + 3)),
      volume_openCubeSet_originCube]
  have hlower : ENNReal.ofReal (((3 : ℝ) ^ n) ^ d) ≤
      volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
        openCubeSet (originCube d m))) := by
    have hchild := measure_mono (μ := (volume : Measure (Vec d)))
      (child_subset_anchorWindowInner hgeom)
    rwa [volume_image_add_openCubeSet x (originCube d n),
      volume_openCubeSet_originCube] at hchild
  refine le_trans hupper (le_trans ?_ (mul_le_mul' le_rfl hlower))
  rw [← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hsplit

/-- The inner window `W` has positive volume. -/
theorem volume_anchorWindowInner_ne_zero {n m : ℤ} {x z : Vec d}
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m)) :
    volume ((((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
      openCubeSet (originCube d m))) ≠ 0 := by
  intro hzero
  have hchild := measure_mono (μ := (volume : Measure (Vec d)))
    (child_subset_anchorWindowInner hgeom)
  rw [hzero, le_zero_iff] at hchild
  exact volume_image_add_openCubeSet_ne_zero x (originCube d n) hchild

/-- Both windows have finite volume. -/
theorem volume_anchorWindow_ne_top (j m : ℤ) (z : Vec d) :
    volume ((((fun y' => z + y') '' openCubeSet (originCube d j)) ∩
      openCubeSet (originCube d m))) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (volume_openCubeSet_ne_top (originCube d m)) ?_
  exact measure_mono (μ := (volume : Measure (Vec d))) Set.inter_subset_right

/-- **The Gagliardo window move.**  The Gagliardo seminorm on `W` is at
most `9^d` times the one on `W'`. -/
theorem normalizedGagliardoESeminormOn_anchorWindow_le
    {n m : ℤ} {x z : Vec d} [NormedSpace ℝ E]
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
    (s : ℝ) (f : Vec d → E) :
    Support.normalizedGagliardoESeminormOn
        ((((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
          openCubeSet (originCube d m))) s f ≤
      ENNReal.ofReal (windowMoveConst d) *
        Support.normalizedGagliardoESeminormOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
            openCubeSet (originCube d m))) s f := by
  have hbase := normalizedGagliardoESeminormOn_le_of_volume_le
    (K := ENNReal.ofReal ((81 : ℝ) ^ d)) (anchorWindowInner_subset_anchorWindow n m z)
    (by simp) (by simp) (volume_anchorWindow_le hgeom) s f
  rwa [ofReal_eightyOne_pow_rpow_half d] at hbase

/-- **The `L²` window move.**  The mean-subtracted normalized `L²` norm on `W`
is at most `2 · 9^d` times the one on `W'`. -/
theorem eLpNorm_sub_volumeAverage_anchorWindow_le {n m : ℤ} {x z : Vec d}
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
    {f : Vec d → ℝ}
    (hf : AEStronglyMeasurable f (Support.normalizedVolumeMeasureOn
      ((((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
        openCubeSet (originCube d m))))) :
    eLpNorm (fun y => f y - volumeAverage
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
            openCubeSet (originCube d m))) f) 2
        (Support.normalizedVolumeMeasureOn
          ((((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
            openCubeSet (originCube d m)))) ≤
      ENNReal.ofReal (2 * windowMoveConst d) *
        eLpNorm (fun y => f y - volumeAverage
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m))) f) 2
          (Support.normalizedVolumeMeasureOn
            ((((fun y' => z + y') '' openCubeSet (originCube d (n + 3))) ∩
              openCubeSet (originCube d m)))) := by
  have hbase := eLpNorm_sub_volumeAverage_le_of_subset
    (K := ENNReal.ofReal ((81 : ℝ) ^ d)) (anchorWindowInner_subset_anchorWindow n m z)
    (by simp) (by simp) (volume_anchorWindow_le hgeom)
    (volume_anchorWindowInner_ne_zero hgeom) (volume_anchorWindow_ne_top (n + 2) m z) hf
  rw [ofReal_eightyOne_pow_rpow_half d] at hbase
  refine le_trans hbase (le_of_eq ?_)
  congr 1
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

end

end Algsuperdiff.Section4.Provider.ExcessDecay
