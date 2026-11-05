/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OffGridComposeCover
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OffGridComposeDepth

/-!
# OffGridComposeAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The composed off-grid stability estimate

This is the composition the printed transport `e.mathcalE.stability.applied`
(ABK26) performs, at an **arbitrary real translate**:

```
𝓔_{t,∞,2}(w + □_k; a, ā)  ≤  C(d,t,u)^{1/2} · 3^{u·(K − k)} · 𝓔_{u,∞,2}(□_K; a, ā)
```

The constant is `offGridStabilityConst d t u = 36dt/((t−u)(1−2u))`, which at the
printed slot `(t,u) = (s/6, s/8)` is at most `192 d` for `s ∈ (0,1]` — a pure
`C(d)`, with **no** `s`-power deviation from the printed constant
(`offGridStabilityConst_slot_le`).  The pieces:

| step | file | output |
| --- | --- | --- |
| per-cube cap | `OffGridStabilityCap` | `3^{2u(K − scale Q)}·𝓔_u²` |
| covering | `OffGridComposeCover` | doubled response across the maximal cubes |
| packing + depth sum | `OffGridComposeDepth` | `12d/(1−2u)` |
| outer shell sum | `OffGridStabilityArith` | `3t/(t−u)` |
| product | here | `36dt/((t−u)(1−2u))` |

Both depths of the printed display (`K − k = 1` and `K − k = 2`) are covered:
the statements quantify over an arbitrary containing grid cube.

## Main results

* `offGridBlockResponseMax_le_cap` — the one-cube off-grid bound.
* `offGridShellMax_le_cap` — the shell bound, in the `A·3^{2ul}` shape.
* `offGridErrorFunctional_le` — **the composed off-grid stability estimate.**
* `offGridErrorFunctional_le_slot` — the same at the printed slot
  `(t,u) = (s/6, s/8)`, with the printed constant `192 d`.

## References

* ABK26, `e.mathcalE.stability.applied`.
* ABK26, `l.lambdas.stability`.
* ABK26, `e.bound.one.cube.by.lambdas`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- Duplicate of `OffGridStabilityGeometry`'s `private translateSet_mono`. -/
private theorem translateSet_subset {w : Vec d} {S T : Set (Vec d)} (h : S ⊆ T) :
    translateSet w S ⊆ translateSet w T := fun _ hx =>
  mem_translateSet_iff_sub_mem.2 (h (mem_translateSet_iff_sub_mem.1 hx))

omit [NeZero d] in
/-- Duplicate of `StabilityIndexCube`'s `private rpow_three_sq`. -/
private theorem rpow_three_sq_aux (y : ℝ) : ((3 : ℝ) ^ y) ^ 2 = (3 : ℝ) ^ (y * 2) := by
  have hy : y * 2 = y + y := by ring
  rw [hy, Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  ring

/-- A real translate of a grid cube inside a grid cube is not coarser. -/
private theorem scale_le_of_translateSet_cubeSet_subset {w : Vec d} {P K : TriadicCube d}
    (h : translateSet w (cubeSet P) ⊆ cubeSet K) : P.scale ≤ K.scale := by
  have hvol : (volume (translateSet w (cubeSet P))).toReal ≤ (volume (cubeSet K)).toReal :=
    ENNReal.toReal_mono (volume_cubeSet_lt_top K).ne (measure_mono h)
  rw [volume_translateSet_eq, volume_cubeSet_toReal, volume_cubeSet_toReal,
    cubeVolume_eq_pow_scale, cubeVolume_eq_pow_scale] at hvol
  by_contra hcon
  push Not at hcon
  have hlt : (3 : ℝ) ^ K.scale < (3 : ℝ) ^ P.scale :=
    zpow_lt_zpow_right₀ (by norm_num) hcon
  have hKpos : (0 : ℝ) < (3 : ℝ) ^ K.scale := zpow_pos (by norm_num) K.scale
  have hpow : ((3 : ℝ) ^ K.scale) ^ d < ((3 : ℝ) ^ P.scale) ^ d :=
    pow_lt_pow_left₀ hlt hKpos.le (NeZero.ne d)
  exact absurd hvol (not_le.2 hpow)

/-! ## 1. The one-cube off-grid bound -/

/-- **The off-grid one-cube estimate.**

For an arbitrary real translate `w + R` contained in the grid cube `K`,

```
max_{|e|=1} 𝐉(w + R, …)  ≤  (12d/(1−2u))·3^{2u(K.scale − R.scale)}·𝓔_{u,∞,2}(K)² .
```

The covering, the per-cube cap (`OffGridStabilityCap`) and the packing/depth sum
composed; the majorant and summability interfaces of the countable subadditivity
are discharged here. -/
theorem offGridBlockResponseMax_le_cap {w : Vec d} {R K : TriadicCube d}
    {g : CoeffField d} {lam Lam : ℝ} (A : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {u : ℝ} (hu0 : 0 < u) (hu : u < 1 / 2)
    (hg : ∀ S : TriadicCube d, (A.coeffOn S).toCoeffField = g)
    (hEll : IsEllipticFieldOn lam Lam (offGridCube w R) g)
    (hKsub : offGridCube w R ⊆ cubeSet K) (hRK : R.scale ≤ K.scale) :
    offGridBlockResponseMax w R g a0 ≤
      12 * (d : ℝ) / (1 - 2 * u) *
        ((3 : ℝ) ^ (2 * u * (((K.scale - R.scale).toNat : ℕ) : ℝ)) *
          Ch02.HomogenizationErrorOnCube K u .infinity (.finite 2) A a0 ^ 2) := by
  classical
  set E : ℝ := Ch02.HomogenizationErrorOnCube K u .infinity (.finite 2) A a0 with hE
  set c : ℝ := (3 : ℝ) ^ (2 * u * (((K.scale - R.scale).toNat : ℕ) : ℝ)) * E ^ 2 with hc
  have hcnn : 0 ≤ c := by
    rw [hc]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (sq_nonneg _)
  set B : TriadicCube d → ℝ := fun Q =>
    c * (3 : ℝ) ^ (2 * u * (((R.scale - Q.scale).toNat : ℕ) : ℝ)) with hB
  -- the per-cube cap, in the factored form the depth sum consumes
  have hcap : ∀ Q : TriadicCube d, MaximalCubeIn (offGridCube w R) Q →
      Ch02.normalizedBlockResponseMax Q A a0 ≤ B Q := by
    intro Q hQ
    have hQR : Q.scale ≤ R.scale := scale_le_of_maximalCubeIn_offGridCube hQ
    have hQK : Q.scale ≤ K.scale := le_trans hQR hRK
    have hsub : cubeSet Q ⊆ cubeSet K := hQ.1.trans hKsub
    have hraw := normalizedBlockResponseMax_le_rpow_mul_homogenizationErrorOnCube_sq
      (P := K) (Q := Q) A a0 hu0 hsub hQK
    have hdepth : (K.scale - Q.scale).toNat =
        (K.scale - R.scale).toNat + (R.scale - Q.scale).toNat := by omega
    have hsplit : (3 : ℝ) ^ (u * (((K.scale - Q.scale).toNat : ℕ) : ℝ) * 2) =
        (3 : ℝ) ^ (2 * u * (((K.scale - R.scale).toNat : ℕ) : ℝ)) *
          (3 : ℝ) ^ (2 * u * (((R.scale - Q.scale).toNat : ℕ) : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      rw [hdepth]
      push_cast
      ring
    have hBeq : B Q = (3 : ℝ) ^ (u * (((K.scale - Q.scale).toNat : ℕ) : ℝ) * 2) * E ^ 2 := by
      rw [hB, hc, hsplit]
      ring
    rw [hBeq]
    exact hraw
  -- the depth sum supplies summability and the value
  obtain ⟨hsum, hle⟩ := summable_and_tsum_maximalCubes_cap_le w R hu0 hu hcnn
  have hBsum : Summable fun Q : maximalCubes (offGridCube w R) =>
      cubeVolume (Q : TriadicCube d) * B (Q : TriadicCube d) := hsum
  have hBle : (∑' Q : maximalCubes (offGridCube w R),
      cubeVolume (Q : TriadicCube d) * B (Q : TriadicCube d)) ≤
      c * (12 * (d : ℝ) * cubeVolume R / (1 - 2 * u)) := hle
  have hcover := offGridBlockResponseMax_le_tsum_maximalCubes (K := K) A a0 hg hEll hKsub hRK
    B hcap hBsum
  have hinv : (0 : ℝ) ≤ (cubeVolume R)⁻¹ := inv_nonneg.2 (cubeVolume_pos R).le
  have hfinal : (cubeVolume R)⁻¹ * (c * (12 * (d : ℝ) * cubeVolume R / (1 - 2 * u))) =
      12 * (d : ℝ) / (1 - 2 * u) * c := by
    have hv : cubeVolume R ≠ 0 := (cubeVolume_pos R).ne'
    have hden : (1 : ℝ) - 2 * u ≠ 0 := by
      have : (0 : ℝ) < 1 - 2 * u := by linarith only [hu]
      exact this.ne'
    field_simp
  calc offGridBlockResponseMax w R g a0
      ≤ (cubeVolume R)⁻¹ * ∑' Q : maximalCubes (offGridCube w R),
          cubeVolume (Q : TriadicCube d) * B (Q : TriadicCube d) := hcover
    _ ≤ (cubeVolume R)⁻¹ * (c * (12 * (d : ℝ) * cubeVolume R / (1 - 2 * u))) :=
        mul_le_mul_of_nonneg_left hBle hinv
    _ = 12 * (d : ℝ) / (1 - 2 * u) * c := hfinal

/-! ## 2. The shell bound -/

/-- **The shell bound of the off-grid cube**, in the `M l ≤ A·3^{2ul}` shape the
outer geometric sum of the exponent bookkeeping consumes. -/
theorem offGridShellMax_le_cap {w : Vec d} {P K : TriadicCube d} {g : CoeffField d}
    {lam Lam : ℝ} (A : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {u : ℝ} (hu0 : 0 < u) (hu : u < 1 / 2)
    (hg : ∀ S : TriadicCube d, (A.coeffOn S).toCoeffField = g)
    (hEll : IsEllipticFieldOn lam Lam (translateSet w (cubeSet P)) g)
    (hcontain : translateSet w (cubeSet P) ⊆ cubeSet K) (l : ℕ) :
    offGridShellMax w P (P.scale - (l : ℤ)) g a0 ≤
      (12 * (d : ℝ) / (1 - 2 * u) *
        ((3 : ℝ) ^ (2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
          Ch02.HomogenizationErrorOnCube K u .infinity (.finite 2) A a0 ^ 2)) *
        (3 : ℝ) ^ (2 * u * (l : ℝ)) := by
  have hPK : P.scale ≤ K.scale := scale_le_of_translateSet_cubeSet_subset hcontain
  refine offGridShellMax_le (by omega) ?_
  intro R hR
  have hRscale : R.scale = P.scale - (l : ℤ) :=
    descendant_scale_eq_of_mem_descendantsAtScale hR
  have hRsub : cubeSet R ⊆ cubeSet P :=
    cubeSet_subset_of_mem_descendantsAtScale (by omega) hR
  have hPsub : offGridCube w R ⊆ translateSet w (cubeSet P) :=
    subset_trans (translateSet_subset (openCubeSet_subset_cubeSet R))
      (translateSet_subset hRsub)
  have hKsub : offGridCube w R ⊆ cubeSet K := hPsub.trans hcontain
  have hRK : R.scale ≤ K.scale := by omega
  have hEllR : IsEllipticFieldOn lam Lam (offGridCube w R) g :=
    IsEllipticFieldOn.mono hEll (isOpen_offGridCube w R).measurableSet hPsub
  have hbase := offGridBlockResponseMax_le_cap (w := w) (R := R) (K := K) A a0 hu0 hu hg
    hEllR hKsub hRK
  have hdepth : (K.scale - R.scale).toNat = (K.scale - P.scale).toNat + l := by omega
  have hsplit : (3 : ℝ) ^ (2 * u * (((K.scale - R.scale).toNat : ℕ) : ℝ)) =
      (3 : ℝ) ^ (2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
        (3 : ℝ) ^ (2 * u * (l : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    rw [hdepth]
    push_cast
    ring
  rw [hsplit] at hbase
  calc offGridBlockResponseMax w R g a0
      ≤ 12 * (d : ℝ) / (1 - 2 * u) *
          ((3 : ℝ) ^ (2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
            (3 : ℝ) ^ (2 * u * (l : ℝ)) *
            Ch02.HomogenizationErrorOnCube K u .infinity (.finite 2) A a0 ^ 2) := hbase
    _ = (12 * (d : ℝ) / (1 - 2 * u) *
          ((3 : ℝ) ^ (2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
            Ch02.HomogenizationErrorOnCube K u .infinity (.finite 2) A a0 ^ 2)) *
          (3 : ℝ) ^ (2 * u * (l : ℝ)) := by ring

/-! ## 3. The composed estimate -/

/-- **The composed off-grid stability estimate** — the tex's
`e.mathcalE.stability.applied` shape at an arbitrary real translate `w`:

```
𝓔_{t,∞,2}(w + □_k; a, ā)
    ≤ (36dt/((t−u)(1−2u)))^{1/2} · 3^{u·(K − k)} · 𝓔_{u,∞,2}(□_K; a, ā) ,
```

valid whenever `w + □_k ⊆ □_K` and `0 < u < t ≤ 1/2`, with the same coefficient
family and the same comparator on both sides.  Both printed depths
(`K − k = 1, 2`) are instances. -/
theorem offGridErrorFunctional_le {w : Vec d} {P K : TriadicCube d} {g : CoeffField d}
    {lam Lam : ℝ} (A : Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {t u : ℝ} (hu0 : 0 < u) (hut : u < t) (ht : t ≤ 1 / 2)
    (hg : ∀ S : TriadicCube d, (A.coeffOn S).toCoeffField = g)
    (hEll : IsEllipticFieldOn lam Lam (translateSet w (cubeSet P)) g)
    (hcontain : translateSet w (cubeSet P) ⊆ cubeSet K) :
    offGridErrorFunctional w P t g a0 ≤
      Real.sqrt (offGridStabilityConst d t u) *
        ((3 : ℝ) ^ (u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) *
          Ch02.HomogenizationErrorOnCube K u .infinity (.finite 2) A a0) := by
  have hu : u < 1 / 2 := lt_of_lt_of_le hut ht
  set E : ℝ := Ch02.HomogenizationErrorOnCube K u .infinity (.finite 2) A a0 with hE
  have hEnn : 0 ≤ E := homogenizationErrorOnCube_infinity_two_nonneg K A a0 hu0
  set Y : ℝ := (3 : ℝ) ^ (u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) with hY
  have hYnn : 0 ≤ Y := Real.rpow_nonneg (by norm_num) _
  set Acap : ℝ := 12 * (d : ℝ) / (1 - 2 * u) * (Y ^ 2 * E ^ 2) with hAcap
  have hden : (0 : ℝ) < 1 - 2 * u := by linarith only [hu]
  have hAnn : 0 ≤ Acap := by
    have hd : (0 : ℝ) ≤ 12 * (d : ℝ) / (1 - 2 * u) := by positivity
    exact mul_nonneg hd (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hYsq : Y ^ 2 = (3 : ℝ) ^ (2 * u * (((K.scale - P.scale).toNat : ℕ) : ℝ)) := by
    rw [hY, rpow_three_sq_aux]
    congr 1
    ring
  have hshell : ∀ l : ℕ, offGridShellMax w P (P.scale - (l : ℤ)) g a0 ≤
      Acap * (3 : ℝ) ^ (2 * u * (l : ℝ)) := by
    intro l
    rw [hAcap, hYsq]
    exact offGridShellMax_le_cap A a0 hu0 hu hg hEll hcontain l
  obtain ⟨-, hseries⟩ := tsum_geometricWeight_two_mul_le (t := t) (u := u) (A := Acap)
    hu0 hut ht hAnn (fun l => offGridShellMax w P (P.scale - (l : ℤ)) g a0)
    (fun l => offGridShellMax_nonneg w P _ g a0) hshell
  have hconst : 3 * t / (t - u) * Acap = offGridStabilityConst d t u * (Y ^ 2 * E ^ 2) := by
    have htu : (0 : ℝ) < t - u := by linarith only [hut]
    rw [hAcap, offGridStabilityConst]
    field_simp
    ring
  have hCnn : 0 ≤ offGridStabilityConst d t u :=
    offGridStabilityConst_nonneg hu0 hut ht
  have hsqrt : Real.sqrt (offGridStabilityConst d t u * (Y ^ 2 * E ^ 2)) =
      Real.sqrt (offGridStabilityConst d t u) * (Y * E) := by
    have hyz : Y ^ 2 * E ^ 2 = (Y * E) ^ 2 := by ring
    rw [hyz, Real.sqrt_mul hCnn, Real.sqrt_sq (mul_nonneg hYnn hEnn)]
  rw [offGridErrorFunctional]
  refine le_trans (Real.sqrt_le_sqrt (le_trans hseries (le_of_eq hconst))) ?_
  rw [hsqrt]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
