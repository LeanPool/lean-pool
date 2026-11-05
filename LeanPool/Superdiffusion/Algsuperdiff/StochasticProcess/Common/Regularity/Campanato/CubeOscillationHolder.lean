/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Campanato.CubeTelescope
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Campanato.OscillationHolder

/-!
# CubeOscillationHolder

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# From clipped oscillation decay to a Hölder seminorm on the whole cube

The Campanato/Morrey embedding, run on the windows clipped to a cube.  Because
the windows are clipped, the estimate is available at **every** centre of the
cube, including centres arbitrarily close to its boundary, and the resulting
Hölder seminorm bound is therefore a bound on the whole open cube rather than on
an interior sub-cube.

The two-point argument is the unclipped one: two centres at distance at most the
bracketing radius have their windows inside a common window of three times that
radius, taken at the first of the two centres and clipped to the same cube.  The
only change is the price of each comparison, which is `ballVolumePrice 6 d`
instead of `ballVolumePrice 3 d` because a clipped window may be half as wide as
the unclipped one in every direction.

The chaining step is unchanged and is reused verbatim: it is a statement about a
two-point bound on a convex set and knows nothing about windows.

## Main definitions

* `clipLocalHolderConstant d α` — the explicit constant of the two-point bound.

## Main results

* `abs_campanatoRepresentative_sub_le_clip` — the two-point bound for
  separations at most `R`, valid up to the boundary of the cube.
* `holderSeminormBoundOn_clip_campanatoRepresentative` — the embedding on a
  convex subset of the cube.
* `holderSeminormBoundOn_cube_campanatoRepresentative` — the embedding on the
  whole open cube.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Campanato

open MeasureTheory HCPolySupport Filter Topology
open Algsuperdiff.Section4.Support
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported

noncomputable section

variable {d : ℕ}

/-! ## 1. The local two-point bound -/

/-- **The constant of the two-point Hölder bound on clipped windows.**  The two
summands are the geometric tail of the telescope and the enclosing-window
comparison at the two centres; the outer factor `3 ^ α` converts the bracketing
radius into the separation. -/
def clipLocalHolderConstant (d : ℕ) (alpha : ℝ) : ℝ :=
  2 * (3 : ℝ) ^ alpha * (campanatoTailConstant alpha + (3 : ℝ) ^ alpha) *
    ballVolumePrice 6 d

theorem clipLocalHolderConstant_nonneg (d : ℕ) {alpha : ℝ} (halpha : 0 < alpha) :
    0 ≤ clipLocalHolderConstant d alpha := by
  refine mul_nonneg (mul_nonneg (by positivity) ?_) (ballVolumePrice_nonneg 6 d)
  exact add_nonneg (campanatoTailConstant_pos halpha).le (Real.rpow_nonneg (by norm_num) _)

/-- **The two-point Hölder bound on the clipped windows.**  Both centres are
arbitrary points of `S`, so the bound holds up to the boundary of the cube. -/
theorem abs_campanatoRepresentative_sub_le_clip
    {c : Vec d} {Rm : ℝ} {S : Set (Vec d)} {R Rtop alpha K : ℝ} {f : Vec d → ℝ}
    (hR : 0 < R) (hRtop : 3 * R ≤ Rtop) (hRtopRm : Rtop ≤ Rm) (halpha : 0 < alpha)
    (hK : 0 ≤ K) (hS : S ⊆ Metric.ball c Rm)
    (hf : MemLp f 2 (volume.restrict (Metric.ball c Rm)))
    (hcamp : HasClipCampanatoDecayOn c Rm S Rtop alpha K f)
    {x y : Vec d} (hx : x ∈ S) (hy : y ∈ S) (hxy : ‖x - y‖ ≤ R) :
    |campanatoRepresentative f R x - campanatoRepresentative f R y| ≤
      clipLocalHolderConstant d alpha * K * ‖x - y‖ ^ alpha := by
  have hRRtop : R ≤ Rtop := by linarith only [hR, hRtop]
  rcases eq_or_lt_of_le (norm_nonneg (x - y)) with hzero | hrho
  · have hxeq : x = y := sub_eq_zero.mp (norm_eq_zero.mp hzero.symm)
    subst hxeq
    simp only [sub_self, abs_zero, norm_zero, Real.zero_rpow halpha.ne', mul_zero]
    exact le_rfl
  obtain ⟨k, hklo, hkhi⟩ := exists_triadicRadius_bracket hR hrho hxy
  have hrk : 0 < triadicRadius R k := triadicRadius_pos hR k
  have hrkR : triadicRadius R k ≤ R := triadicRadius_le hR.le k
  have hrkRm : triadicRadius R k ≤ Rm := by
    linarith only [hrkR, hRRtop, hRtopRm]
  have h3pos : 0 < 3 * triadicRadius R k := by linarith only [hrk]
  have h3Rtop : 3 * triadicRadius R k ≤ Rtop := by linarith only [hrkR, hRtop]
  have h3Rm : 3 * triadicRadius R k ≤ Rm := by linarith only [h3Rtop, hRtopRm]
  have hkappa : 2 * (3 * triadicRadius R k) ≤ 6 * triadicRadius R k := by
    linarith only [hrk]
  have hsubx : clipBall c Rm x (triadicRadius R k) ⊆
      clipBall c Rm x (3 * triadicRadius R k) :=
    Set.inter_subset_inter_left _ (Metric.ball_subset_ball (by linarith only [hrk]))
  have hsuby : clipBall c Rm y (triadicRadius R k) ⊆
      clipBall c Rm x (3 * triadicRadius R k) := by
    refine Set.inter_subset_inter_left _ (Metric.ball_subset_ball' ?_)
    rw [dist_eq_norm, norm_sub_rev]
    linarith only [hkhi, hrk]
  have hmeanx := abs_volumeAverage_clipBall_sub_le (kappa := 6) hrk hrkRm (hS hx)
    h3pos h3Rm (hS hx) hsubx hkappa hf
  have hmeany := abs_volumeAverage_clipBall_sub_le (kappa := 6) hrk hrkRm (hS hy)
    h3pos h3Rm (hS hx) hsuby hkappa hf
  have hosc := hcamp x hx (3 * triadicRadius R k) h3pos h3Rtop
  have hsplit : (3 * triadicRadius R k) ^ alpha =
      (3 : ℝ) ^ alpha * triadicRadius R k ^ alpha :=
    Real.mul_rpow (by norm_num) hrk.le
  have hoscsplit : normalizedL2On (clipBall c Rm x (3 * triadicRadius R k))
      (fun z => f z - volumeAverage (clipBall c Rm x (3 * triadicRadius R k)) f) ≤
      K * ((3 : ℝ) ^ alpha * triadicRadius R k ^ alpha) := by
    rwa [hsplit] at hosc
  have hprice6 : (0 : ℝ) ≤ ballVolumePrice 6 d := ballVolumePrice_nonneg 6 d
  have hB : |clipCampanatoAverage c Rm f R x k -
      volumeAverage (clipBall c Rm x (3 * triadicRadius R k)) f| ≤
      ballVolumePrice 6 d * (K * ((3 : ℝ) ^ alpha * triadicRadius R k ^ alpha)) :=
    hmeanx.trans (mul_le_mul_of_nonneg_left hoscsplit hprice6)
  have hC : |volumeAverage (clipBall c Rm x (3 * triadicRadius R k)) f -
      clipCampanatoAverage c Rm f R y k| ≤
      ballVolumePrice 6 d * (K * ((3 : ℝ) ^ alpha * triadicRadius R k ^ alpha)) := by
    rw [abs_sub_comm]
    exact hmeany.trans (mul_le_mul_of_nonneg_left hoscsplit hprice6)
  have htailx := dist_clipCampanatoAverage_representative_le hR hRRtop hRtopRm halpha
    hS hf hcamp hx k
  have htaily := dist_clipCampanatoAverage_representative_le hR hRRtop hRtopRm halpha
    hS hf hcamp hy k
  have hA : |campanatoRepresentative f R x - clipCampanatoAverage c Rm f R x k| ≤
      campanatoTailConstant alpha * ballVolumePrice 6 d * K *
        triadicRadius R k ^ alpha := by
    rw [abs_sub_comm, ← Real.dist_eq]
    exact htailx
  have hE : |clipCampanatoAverage c Rm f R y k - campanatoRepresentative f R y| ≤
      campanatoTailConstant alpha * ballVolumePrice 6 d * K *
        triadicRadius R k ^ alpha := by
    rw [← Real.dist_eq]
    exact htaily
  have htri : |campanatoRepresentative f R x - campanatoRepresentative f R y| ≤
      |campanatoRepresentative f R x - clipCampanatoAverage c Rm f R x k| +
        |clipCampanatoAverage c Rm f R x k -
          volumeAverage (clipBall c Rm x (3 * triadicRadius R k)) f| +
        |volumeAverage (clipBall c Rm x (3 * triadicRadius R k)) f -
          clipCampanatoAverage c Rm f R y k| +
        |clipCampanatoAverage c Rm f R y k - campanatoRepresentative f R y| := by
    have hid : campanatoRepresentative f R x - campanatoRepresentative f R y =
        (campanatoRepresentative f R x - clipCampanatoAverage c Rm f R x k) +
          (clipCampanatoAverage c Rm f R x k -
            volumeAverage (clipBall c Rm x (3 * triadicRadius R k)) f) +
          (volumeAverage (clipBall c Rm x (3 * triadicRadius R k)) f -
            clipCampanatoAverage c Rm f R y k) +
          (clipCampanatoAverage c Rm f R y k - campanatoRepresentative f R y) := by ring
    have habs : ∀ a b e g : ℝ, |a + b + e + g| ≤ |a| + |b| + |e| + |g| := by
      intro a b e g
      calc |a + b + e + g| ≤ |a + b + e| + |g| := abs_add_le _ _
        _ ≤ |a| + |b| + |e| + |g| := add_le_add (abs_add_three a b e) le_rfl
    rw [hid]
    exact habs _ _ _ _
  have hcollect : |campanatoRepresentative f R x - campanatoRepresentative f R y| ≤
      2 * (campanatoTailConstant alpha + (3 : ℝ) ^ alpha) * ballVolumePrice 6 d * K *
        triadicRadius R k ^ alpha := by
    have hsum := htri.trans (add_le_add (add_le_add (add_le_add hA hB) hC) hE)
    refine hsum.trans_eq ?_
    ring
  have hbracket : triadicRadius R k ≤ 3 * ‖x - y‖ := by
    have h := hklo
    rw [triadicRadius_succ] at h
    linarith only [h]
  have hpow : triadicRadius R k ^ alpha ≤ (3 : ℝ) ^ alpha * ‖x - y‖ ^ alpha := by
    have hmono := Real.rpow_le_rpow hrk.le hbracket halpha.le
    rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (norm_nonneg _)] at hmono
  have hcoef : 0 ≤ 2 * (campanatoTailConstant alpha + (3 : ℝ) ^ alpha) *
      ballVolumePrice 6 d * K := by
    have hinner : 0 ≤ campanatoTailConstant alpha + (3 : ℝ) ^ alpha :=
      add_nonneg (campanatoTailConstant_pos halpha).le (Real.rpow_nonneg (by norm_num) _)
    exact mul_nonneg (mul_nonneg (by linarith only [hinner]) hprice6) hK
  refine hcollect.trans ?_
  calc 2 * (campanatoTailConstant alpha + (3 : ℝ) ^ alpha) * ballVolumePrice 6 d * K *
        triadicRadius R k ^ alpha
      ≤ 2 * (campanatoTailConstant alpha + (3 : ℝ) ^ alpha) * ballVolumePrice 6 d * K *
        ((3 : ℝ) ^ alpha * ‖x - y‖ ^ alpha) := mul_le_mul_of_nonneg_left hpow hcoef
    _ = clipLocalHolderConstant d alpha * K * ‖x - y‖ ^ alpha := by
      rw [clipLocalHolderConstant]
      ring

/-! ## 2. The embedding -/

/-- **The Campanato/Morrey embedding on a convex subset of the cube.** -/
theorem holderSeminormBoundOn_clip_campanatoRepresentative
    {c : Vec d} {Rm : ℝ} {S W : Set (Vec d)} {R Rtop alpha K : ℝ} {N : ℕ}
    {f : Vec d → ℝ}
    (hR : 0 < R) (hRtop : 3 * R ≤ Rtop) (hRtopRm : Rtop ≤ Rm) (halpha : 0 < alpha)
    (hK : 0 ≤ K) (hS : S ⊆ Metric.ball c Rm)
    (hW : Convex ℝ W) (hWS : W ⊆ S) (hN : 0 < N)
    (hdiam : ∀ x ∈ W, ∀ y ∈ W, ‖x - y‖ ≤ (N : ℝ) * R)
    (hf : MemLp f 2 (volume.restrict (Metric.ball c Rm)))
    (hcamp : HasClipCampanatoDecayOn c Rm S Rtop alpha K f) :
    HolderSeminormBoundOn W alpha
      ((N : ℝ) ^ (1 - alpha) * (clipLocalHolderConstant d alpha * K))
      (campanatoRepresentative f R) :=
  holderSeminormBoundOn_of_local_of_convex hW hN hdiam
    (fun _x hx _y hy hxy =>
      abs_campanatoRepresentative_sub_le_clip hR hRtop hRtopRm halpha hK hS hf hcamp
        (hWS hx) (hWS hy) hxy)

/-- **The embedding on the whole open cube.**  The chain length `N` absorbs the
ratio between the diameter `2 Rm` of the cube and the top radius `R` of the
telescope. -/
theorem holderSeminormBoundOn_cube_campanatoRepresentative
    {c : Vec d} {Rm : ℝ} {R Rtop alpha K : ℝ} {N : ℕ} {f : Vec d → ℝ}
    (hR : 0 < R) (hRtop : 3 * R ≤ Rtop) (hRtopRm : Rtop ≤ Rm) (halpha : 0 < alpha)
    (hK : 0 ≤ K) (hN : 0 < N) (hchain : 2 * Rm ≤ (N : ℝ) * R)
    (hf : MemLp f 2 (volume.restrict (Metric.ball c Rm)))
    (hcamp : HasClipCampanatoDecayOn c Rm (Metric.ball c Rm) Rtop alpha K f) :
    HolderSeminormBoundOn (Metric.ball c Rm) alpha
      ((N : ℝ) ^ (1 - alpha) * (clipLocalHolderConstant d alpha * K))
      (campanatoRepresentative f R) :=
  holderSeminormBoundOn_clip_campanatoRepresentative hR hRtop hRtopRm halpha hK
    (subset_refl _) (convex_ball c Rm) (subset_refl _) hN
    (fun _x hx _y hy => (norm_sub_le_two_mul_of_mem_ball hx hy).trans hchain) hf hcamp

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Campanato
