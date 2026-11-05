/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.InteriorGlueWindow

/-!
# InteriorWindowMove

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Gagliardo window move: the child window into the anchor's parent window

`InteriorGlueWindow` restricts the anchor's clause-(iv) *data* from `□_m` to a
sub-window — a membership transport, no constant.  This module supplies the
opposite, quantitative move on the *seminorm* itself, which the assembly needs on
the correction and forcing legs:

```text
  [g]_{H^s(x+□_n)}  ≤  3^{d} · [g]_{H^s(W)} ,      W = (z+□_{n+2}) ∩ □_m ,
```

whenever the anchor's geometry binder holds.  The mechanism is the volume
normalization alone: the Gagliardo measure of a window `A` is
`|A|^{-1}(vol⊗vol)|_{A×A}`, so passing from `W` to the smaller `x+□_n` costs
exactly the volume ratio `|W|/|x+□_n| ≤ 3^{2d}` inside an `L²`, i.e. `3^{d}`.

The ratio is the *two-scale* one because the anchor's own geometry binder puts
the child `x+□_n` inside `z+□_{n+1}`, hence inside `z+□_{n+2}`, which carries
`W`; the crude bound `|W| ≤ |□_{n+2}| = 3^{2d}|□_n|` is used, so the constant is
`3^{d}` and not the `3^{2d}` a two-step application would give.

## References

* ABK26, `l.harmonic.approximation.good.scales`, (the geometry binder; the
  right-hand-side windows).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## 1. The volume of an origin cube -/

/-- The open realization of `□_k` has volume `(3^k)^d`. -/
theorem volume_openCubeSet_originCube (k : ℤ) :
    volume (openCubeSet (originCube d k)) = ENNReal.ofReal (((3 : ℝ) ^ k) ^ d) := by
  have hfin : volume (cubeSet (originCube d k)) ≠ ⊤ := (volume_cubeSet_lt_top _).ne
  have htoReal : (volume (cubeSet (originCube d k))).toReal = ((3 : ℝ) ^ k) ^ d := by
    rw [volume_cubeSet_toReal, cubeVolume_eq_pow_scale]
    rfl
  rw [volume_openCubeSet_eq_volume_cubeSet, ← ENNReal.ofReal_toReal hfin, htoReal]

/-- The two-scale volume ratio of the anchor's parent and child cubes. -/
theorem volume_openCubeSet_originCube_add_two_le (n : ℤ) :
    volume (openCubeSet (originCube d (n + 2))) ≤
      ENNReal.ofReal ((9 : ℝ) ^ d) * volume (openCubeSet (originCube d n)) := by
  have hsplit : ((3 : ℝ) ^ (n + 2)) ^ d = (9 : ℝ) ^ d * ((3 : ℝ) ^ n) ^ d := by
    rw [← mul_pow]
    congr 1
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0) n 2]
    norm_num
    ring
  rw [volume_openCubeSet_originCube, volume_openCubeSet_originCube, hsplit,
    ENNReal.ofReal_mul (by positivity)]

/-! ## 2. The seminorm under a window shrink -/

/-- **The Gagliardo seminorm on a sub-window, at the volume ratio.**

If `B ⊆ A` and `|A| ≤ K |B|` then `[f]_{H^s(B)} ≤ K^{1/2} [f]_{H^s(A)}`.  Both
sides are `ℝ≥0∞`, so no finiteness is required. -/
theorem normalizedGagliardoESeminormOn_le_of_volume_le {A B : Set (Vec d)} {K : ℝ≥0∞}
    (hAB : B ⊆ A) (hK0 : K ≠ 0) (hKtop : K ≠ ⊤)
    (hvol : volume A ≤ K * volume B) (s : ℝ) (f : Vec d → E) :
    Support.normalizedGagliardoESeminormOn B s f ≤
      K ^ (1 / 2 : ℝ) * Support.normalizedGagliardoESeminormOn A s f := by
  have hinv : (volume B)⁻¹ ≤ K * (volume A)⁻¹ := by
    have h1 : (K * volume B)⁻¹ ≤ (volume A)⁻¹ := ENNReal.inv_le_inv.mpr hvol
    have h2 : K * (K * volume B)⁻¹ = (volume B)⁻¹ := by
      rw [ENNReal.mul_inv (Or.inl hK0) (Or.inl hKtop), ← mul_assoc,
        ENNReal.mul_inv_cancel hK0 hKtop, one_mul]
    calc (volume B)⁻¹ = K * (K * volume B)⁻¹ := h2.symm
      _ ≤ K * (volume A)⁻¹ := mul_le_mul' le_rfl h1
  have hmeas : Support.normalizedGagliardoMeasureOn B ≤
      K • Support.normalizedGagliardoMeasureOn A := by
    rw [normalizedGagliardoMeasureOn_eq_smul_restrict,
      normalizedGagliardoMeasureOn_eq_smul_restrict]
    refine Measure.le_iff'.mpr fun S => ?_
    have hprod : ((volume.prod volume).restrict (B ×ˢ B)) S ≤
        ((volume.prod volume).restrict (A ×ˢ A)) S :=
      Measure.restrict_mono (Set.prod_mono hAB hAB) le_rfl S
    calc ((volume B)⁻¹ • ((volume.prod volume).restrict (B ×ˢ B))) S
        = (volume B)⁻¹ * ((volume.prod volume).restrict (B ×ˢ B)) S := by
          simp only [Measure.smul_apply, smul_eq_mul]
      _ ≤ (K * (volume A)⁻¹) * ((volume.prod volume).restrict (A ×ˢ A)) S :=
          mul_le_mul' hinv hprod
      _ = (K • ((volume A)⁻¹ • ((volume.prod volume).restrict (A ×ˢ A)))) S := by
          simp only [Measure.smul_apply, smul_eq_mul, mul_assoc]
  have hmono : eLpNorm (Gagliardo.gagliardoKernel s 2 f) 2
      (Support.normalizedGagliardoMeasureOn B) ≤
      eLpNorm (Gagliardo.gagliardoKernel s 2 f) 2
        (K • Support.normalizedGagliardoMeasureOn A) :=
    eLpNorm_mono_measure _ hmeas
  have hsmul : eLpNorm (Gagliardo.gagliardoKernel s 2 f) 2
      (K • Support.normalizedGagliardoMeasureOn A) =
      K ^ (1 / 2 : ℝ) * eLpNorm (Gagliardo.gagliardoKernel s 2 f) 2
        (Support.normalizedGagliardoMeasureOn A) := by
    rw [eLpNorm_smul_measure_of_ne_zero_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    norm_num
  rw [Support.normalizedGagliardoESeminormOn_def, Support.normalizedGagliardoESeminormOn_def]
  rw [← hsmul]
  exact hmono

/-! ## 3. The anchor's child-to-parent window move -/

/-- The `d`-only constant of the window move: `3^d`, the square root of the
two-scale volume ratio. -/
def gagliardoWindowConst (d : ℕ) : ℝ := (3 : ℝ) ^ d

theorem gagliardoWindowConst_pos (d : ℕ) : 0 < gagliardoWindowConst d := by
  rw [gagliardoWindowConst]
  positivity

private theorem nine_pow_rpow_half (d : ℕ) :
    ((9 : ℝ) ^ d) ^ (1 / 2 : ℝ) = (3 : ℝ) ^ d := by
  have h9 : (9 : ℝ) ^ d = ((3 : ℝ) ^ d) ^ (2 : ℕ) := by
    rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [h9, ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]

private theorem ofReal_nine_pow_rpow_half (d : ℕ) :
    (ENNReal.ofReal ((9 : ℝ) ^ d)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (gagliardoWindowConst d) := by
  rw [ENNReal.ofReal_rpow_of_pos (by positivity : (0 : ℝ) < (9 : ℝ) ^ d),
    gagliardoWindowConst, nine_pow_rpow_half d]

/-- **The window move.**

Under the anchor's geometry binder, the Gagliardo seminorm on the child window
`x + □_n` is bounded by `3^d` times the seminorm on the anchor's own
right-hand-side window `W = (z+□_{n+2}) ∩ □_m`. -/
theorem normalizedGagliardoESeminormOn_child_le_anchorWindow {n m : ℤ} {x z : Vec d}
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
    (s : ℝ) (f : Vec d → E) :
    Support.normalizedGagliardoESeminormOn
        ((fun y => x + y) '' openCubeSet (originCube d n)) s f ≤
      ENNReal.ofReal (gagliardoWindowConst d) *
        Support.normalizedGagliardoESeminormOn
          (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
            openCubeSet (originCube d m)) s f := by
  have hAB : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
        openCubeSet (originCube d m) := by
    intro p hp
    refine ⟨?_, (hgeom hp).2⟩
    obtain ⟨q, hq, hqp⟩ := (hgeom hp).1
    exact ⟨q, openCubeSet_originCube_subset_of_le (by omega) hq, hqp⟩
  have hvol : volume (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
      openCubeSet (originCube d m)) ≤
      ENNReal.ofReal ((9 : ℝ) ^ d) *
        volume ((fun y => x + y) '' openCubeSet (originCube d n)) := by
    rw [volume_image_add_openCubeSet x (originCube d n)]
    refine le_trans (measure_mono Set.inter_subset_left) ?_
    rw [volume_image_add_openCubeSet z (originCube d (n + 2))]
    exact volume_openCubeSet_originCube_add_two_le n
  have hbase := normalizedGagliardoESeminormOn_le_of_volume_le (K := ENNReal.ofReal ((9 : ℝ) ^ d))
    hAB (by simp) (by simp) hvol s f
  rwa [ofReal_nine_pow_rpow_half d] at hbase

/-- **The window move, in the real-valued form the assembly consumes.**

The finiteness hypothesis is the anchor's own clause (iv), restricted to `W`. -/
theorem normalizedGagliardoESeminormOn_child_toReal_le {n m : ℤ} {x z : Vec d} {s : ℝ}
    (hgeom : (fun y => x + y) '' openCubeSet (originCube d n) ⊆
      ((fun y => z + y) '' openCubeSet (originCube d (n + 1))) ∩
        openCubeSet (originCube d m))
    (f : Vec d → E)
    (hfin : MemLp (Gagliardo.gagliardoKernel s 2 f) 2
      (Support.normalizedGagliardoMeasureOn
        (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
          openCubeSet (originCube d m)))) :
    (Support.normalizedGagliardoESeminormOn
        ((fun y => x + y) '' openCubeSet (originCube d n)) s f).toReal ≤
      gagliardoWindowConst d *
        (Support.normalizedGagliardoESeminormOn
          (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
            openCubeSet (originCube d m)) s f).toReal := by
  have hbase := normalizedGagliardoESeminormOn_child_le_anchorWindow hgeom s f
  have hne : Support.normalizedGagliardoESeminormOn
      (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
        openCubeSet (originCube d m)) s f ≠ ⊤ := hfin.eLpNorm_ne_top
  have hRHSne : ENNReal.ofReal (gagliardoWindowConst d) *
      Support.normalizedGagliardoESeminormOn
        (((fun y' => z + y') '' openCubeSet (originCube d (n + 2))) ∩
          openCubeSet (originCube d m)) s f ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hne
  have htoReal := ENNReal.toReal_mono hRHSne hbase
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (gagliardoWindowConst_pos d).le] at htoReal

end

end Algsuperdiff.Section4.Provider.ExcessDecay
