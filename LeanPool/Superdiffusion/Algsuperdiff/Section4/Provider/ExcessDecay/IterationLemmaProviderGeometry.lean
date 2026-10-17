/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.QuasiMonotone
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SlopeStabilityEndpoints

/-!
# IterationLemmaProviderGeometry

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Window geometry for the iteration-lemma provider: translates, the cap, the normalizers

The frozen iteration anchor states its window family with **arbitrary real translates** of
the centred triadic cubes,

```
x + □_{j−2} ⊆ U_j ⊆ y + □_j        (for every j ≤ m),
```

which is the paper's own hypothesis: `x` and `y` are unconstrained points of
`ℝ^d`, so `x + □_{j−2}` is in general *not* a triadic cube.  The proved
producers come in two flavours --- `axisCube`-based (arbitrary corner,
arbitrary side) and `TriadicCube`-based --- and only the first applies here.
This module proves the three adapters the provider needs:

* **the translate bridge** (`axisCube_sandwich_of_translateSandwich`): a translate of a
  centred origin cube *is* an axis cube, so the anchor's hypothesis yields an `axisCube`
  sandwich of aspect ratio `1/9` at every scale;
* **the `j ≤ m` cap** (`cappedWindows`): the proved engine and the proved
  producers quantify their interface over **all** `k : ℤ`, while the anchor
  supplies window data only for `j ≤ m` (the binding adjudication).  The honest
  adapter is the capped family `U_tilde_k = U_{min(k,m)}`, which agrees with `U` on
  `(−∞, m]`, is nested everywhere, and carries the sandwich at *every* `k`
  because the cap re-uses the scale-`m` cubes;
* **the normalizer bridges** at the `axisCube` sandwich: `3^{−j}`-normalized
  oscillation versus the `|W|^{−1/d}`-normalized one, at the printed aspect
  ratio `3^{−2}`, obtained from the proved arithmetic lemma
  `rpow_normalizer_bounds`.

Nothing here is an estimate: every statement is geometry or measure bookkeeping.

## References

* ABK26, `l.iteration.lemma` statement (the window hypothesis).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport (Vec axisCube openCubeSet originCube TriadicCube volumeAverage)
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ### The translate bridge -/

/-- The centred origin cube `□_j = (−3^j/2, 3^j/2)^d` is the axis cube with corner
`−3^j/2` and side `3^j`. -/
theorem openCubeSet_originCube_eq_axisCube (d : ℕ) (j : ℤ) :
    openCubeSet (originCube d j)
      = axisCube (fun _ => -(1 / 2) * (3 : ℝ) ^ j) ((3 : ℝ) ^ j) := by
  ext z
  simp only [HCPolySupport.mem_openCubeSet_originCube_iff, axisCube, Set.mem_univ_pi,
    Set.mem_Ioo]
  refine forall_congr' fun i => ?_
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith only [h2]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith only [h2]⟩

/-- Translating an axis cube translates its corner. -/
theorem image_add_axisCube (x z : Vec d) (L : ℝ) :
    (fun v => x + v) '' axisCube z L = axisCube (x + z) L := by
  ext y
  simp only [Set.mem_image, axisCube, Set.mem_univ_pi, Set.mem_Ioo, Pi.add_apply]
  constructor
  · rintro ⟨v, hv, rfl⟩
    intro i
    obtain ⟨h1, h2⟩ := hv i
    simp only [Pi.add_apply]
    exact ⟨by linarith only [h1], by linarith only [h2]⟩
  · intro hy
    refine ⟨y - x, fun i => ?_, add_sub_cancel x y⟩
    obtain ⟨h1, h2⟩ := hy i
    simp only [Pi.sub_apply]
    exact ⟨by linarith only [h1], by linarith only [h2]⟩

/-- **The translate bridge.**  The anchor's window hypothesis at a scale `j` --- an
arbitrary translate of `□_{j−2}` inside `W`, and `W` inside an arbitrary translate of
`□_j` --- is an `axisCube` sandwich with sides `3^{j−2}` and `3^j`, i.e. of aspect ratio
`1/9`. -/
theorem axisCube_sandwich_of_translateSandwich {W : Set (Vec d)} {x y : Vec d} {j : ℤ}
    (hin : (fun v => x + v) '' openCubeSet (originCube d (j - 2)) ⊆ W)
    (hout : W ⊆ (fun v => y + v) '' openCubeSet (originCube d j)) :
    ∃ zin zout : Vec d,
      axisCube zin ((3 : ℝ) ^ (j - 2)) ⊆ W ∧ W ⊆ axisCube zout ((3 : ℝ) ^ j) := by
  refine ⟨x + fun _ => -(1 / 2) * (3 : ℝ) ^ (j - 2),
    y + fun _ => -(1 / 2) * (3 : ℝ) ^ j, ?_, ?_⟩
  · rw [← image_add_axisCube, ← openCubeSet_originCube_eq_axisCube]
    exact hin
  · rw [← image_add_axisCube, ← openCubeSet_originCube_eq_axisCube]
    exact hout

/-! ### The `j ≤ m` cap -/

/-- **The capped window family** `U_tilde_k = U_{min(k,m)}`: the honest adapter from the
anchor's `j ≤ m` window data to the `∀ k : ℤ` interface of the proved engine
and the proved producers.  Nothing is invented above `m`: the family is
constant there. -/
def cappedWindows (U : ℤ → Set (Vec d)) (m : ℤ) (k : ℤ) : Set (Vec d) := U (min k m)

theorem cappedWindows_of_le {U : ℤ → Set (Vec d)} {m k : ℤ} (hk : k ≤ m) :
    cappedWindows U m k = U k := by
  rw [cappedWindows, min_eq_left hk]

/-- A family nested one scale at a time below `m` is monotone below `m`. -/
theorem subset_of_le_of_nest {U : ℤ → Set (Vec d)} {m : ℤ}
    (hnest : ∀ j : ℤ, j ≤ m → U (j - 1) ⊆ U j) {a b : ℤ} (hab : a ≤ b) (hbm : b ≤ m) :
    U a ⊆ U b := by
  induction b, hab using Int.leInduction with
  | base => exact subset_rfl
  | succ c hac ih =>
      have hstep : U c ⊆ U (c + 1) := by
        have h := hnest (c + 1) hbm
        rwa [add_sub_cancel_right] at h
      exact (ih (by omega)).trans hstep

/-- The capped family is nested at **every** scale. -/
theorem cappedWindows_nest {U : ℤ → Set (Vec d)} {m : ℤ}
    (hnest : ∀ j : ℤ, j ≤ m → U (j - 1) ⊆ U j) (k : ℤ) :
    cappedWindows U m k ⊆ cappedWindows U m (k + 1) := by
  rw [cappedWindows, cappedWindows]
  exact subset_of_le_of_nest hnest (by omega) (min_le_right _ _)

/-- Every capped window sits inside the top window. -/
theorem cappedWindows_subset_top {U : ℤ → Set (Vec d)} {m : ℤ}
    (hnest : ∀ j : ℤ, j ≤ m → U (j - 1) ⊆ U j) (k : ℤ) :
    cappedWindows U m k ⊆ U m := by
  rw [cappedWindows]
  exact subset_of_le_of_nest hnest (min_le_right _ _) le_rfl

/-! ### Measure-theoretic slots at an `axisCube` sandwich -/

/-- The square of every affine deviation of `u` is integrable on a window contained in an
axis cube.  This is the `hint` slot of `affineExcess_quasiMonotone_of_nested`. -/
theorem integrableOn_sub_affineEval_sq_of_axisCubeSandwich {W : Set (Vec d)}
    {u : Vec d → ℝ} {zout : Vec d} {Lout : ℝ} (hLout : 0 < Lout)
    (hmeas : MeasurableSet W) (hout : W ⊆ axisCube zout Lout)
    (hu : MemLp u 2 (volume.restrict W)) (c : ℝ) (g : Vec d) :
    IntegrableOn (fun x => (u x - affineEval c g x) ^ 2) W := by
  have haff : MemLp (affineEval c g) 2 (volume.restrict W) :=
    memLp_affineEval_of_sandwich hLout hmeas hout c g
  have hmem : MemLp (fun x => u x - affineEval c g x) 2 (volume.restrict W) := hu.sub haff
  exact (memLp_two_iff_integrable_sq hmem.aestronglyMeasurable).1 hmem

/-- **The volume ratio of an `axisCube` sandwich family with a slowly growing scale.**

If `W_k` is sandwiched between axis cubes of sides `3^{s k − 2}` and `3^{s k}` and the
scale function `s` increases by at most one per step, the one-step volume ratio is at most
`3^{3d}`, so the exponent `1/d + 1/2` of the excess normalizers gives the *same* constant
`volumeRatioConstTriadic d` the triadic producer runs at.  This is the `hratio` slot. -/
theorem volumeRatio_le_of_axisCubeSandwich {W : ℤ → Set (Vec d)} {zin zout : ℤ → Vec d}
    {s : ℤ → ℤ} (hs1 : ∀ k : ℤ, s (k + 1) ≤ s k + 1)
    (hin : ∀ k : ℤ, axisCube (zin k) ((3 : ℝ) ^ (s k - 2)) ⊆ W k)
    (hout : ∀ k : ℤ, W k ⊆ axisCube (zout k) ((3 : ℝ) ^ (s k))) :
    ∀ k : ℤ, ((volume (W (k + 1))).toReal / (volume (W k)).toReal) ^ ((d : ℝ)⁻¹ + 1 / 2)
      ≤ volumeRatioConstTriadic d := by
  intro k
  have hexp : (0 : ℝ) ≤ (d : ℝ)⁻¹ + 1 / 2 := by positivity
  have hlowpos : (0 : ℝ) < ((3 : ℝ) ^ (s k - 2)) ^ d := by positivity
  have hlow : ((3 : ℝ) ^ (s k - 2)) ^ d ≤ (volume (W k)).toReal :=
    pow_le_volume_toReal_of_sandwich (le_of_lt (zpow_pos (by norm_num) _)) (hin k) (hout k)
  have hpos : (0 : ℝ) < (volume (W k)).toReal := lt_of_lt_of_le hlowpos hlow
  have hhigh : (volume (W (k + 1))).toReal ≤ ((3 : ℝ) ^ (s (k + 1))) ^ d :=
    volume_toReal_le_pow_of_sandwich (le_of_lt (zpow_pos (by norm_num) _)) (hout (k + 1))
  have hstep : ((3 : ℝ) ^ (s (k + 1))) ^ d ≤ ((3 : ℝ) ^ (s k + 1)) ^ d := by
    have h1 : (3 : ℝ) ^ (s (k + 1)) ≤ (3 : ℝ) ^ (s k + 1) :=
      zpow_le_zpow_right₀ (by norm_num) (hs1 k)
    exact pow_le_pow_left₀ (le_of_lt (zpow_pos (by norm_num) _)) h1 d
  have hquot : ((3 : ℝ) ^ (s k + 1)) ^ d / ((3 : ℝ) ^ (s k - 2)) ^ d = (3 : ℝ) ^ (3 * d) := by
    rw [← div_pow, ← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0),
      show s k + 1 - (s k - 2) = (3 : ℤ) by ring,
      show ((3 : ℝ) ^ (3 : ℤ)) = 3 ^ (3 : ℕ) by norm_num, ← pow_mul]
  have hmul : (volume (W (k + 1))).toReal * ((3 : ℝ) ^ (s k - 2)) ^ d
      ≤ ((3 : ℝ) ^ (s k + 1)) ^ d * (volume (W k)).toReal := by
    have t1 : (volume (W (k + 1))).toReal * ((3 : ℝ) ^ (s k - 2)) ^ d
        ≤ ((3 : ℝ) ^ (s k + 1)) ^ d * ((3 : ℝ) ^ (s k - 2)) ^ d :=
      mul_le_mul_of_nonneg_right (le_trans hhigh hstep) hlowpos.le
    have t2 : ((3 : ℝ) ^ (s k + 1)) ^ d * ((3 : ℝ) ^ (s k - 2)) ^ d
        ≤ ((3 : ℝ) ^ (s k + 1)) ^ d * (volume (W k)).toReal :=
      mul_le_mul_of_nonneg_left hlow (by positivity)
    exact t1.trans t2
  have hratio : (volume (W (k + 1))).toReal / (volume (W k)).toReal ≤ (3 : ℝ) ^ (3 * d) := by
    rw [← hquot, div_le_div_iff₀ hpos hlowpos]
    exact hmul
  rw [volumeRatioConstTriadic]
  exact Real.rpow_le_rpow (by positivity) hratio hexp

/-! ### The normalizer bridges at an `axisCube` sandwich -/

/-- The two volume bounds an `axisCube` sandwich of aspect ratio `1/9` gives, in
the shape the proved normalizer arithmetic consumes. -/
theorem volume_toReal_bounds_of_axisCubeSandwich {W : Set (Vec d)} {zin zout : Vec d}
    {j : ℤ} (hin : axisCube zin ((3 : ℝ) ^ (j - 2)) ⊆ W)
    (hout : W ⊆ axisCube zout ((3 : ℝ) ^ j)) :
    ((3 : ℝ) ^ (j - 2)) ^ d ≤ (volume W).toReal
      ∧ (volume W).toReal ≤ ((3 : ℝ) ^ j) ^ d :=
  ⟨pow_le_volume_toReal_of_sandwich (le_of_lt (zpow_pos (by norm_num) _)) hin hout,
    volume_toReal_le_pow_of_sandwich (le_of_lt (zpow_pos (by norm_num) _)) hout⟩

/-- The `3^{−j}`-normalized oscillation is below the `|W|^{−1/d}`-normalized one,
on a window sandwiched at aspect ratio `1/9`. -/
theorem oscillationScaled_le_oscillationOn_of_axisCubeSandwich (hd : d ≠ 0)
    {W : Set (Vec d)} {zin zout : Vec d} {j : ℤ}
    (hin : axisCube zin ((3 : ℝ) ^ (j - 2)) ⊆ W)
    (hout : W ⊆ axisCube zout ((3 : ℝ) ^ j)) (u : Vec d → ℝ) :
    oscillationScaled j W u ≤ oscillationOn W u := by
  obtain ⟨hlo, hhi⟩ := volume_toReal_bounds_of_axisCubeSandwich (d := d) hin hout
  obtain ⟨hlow, _⟩ := rpow_normalizer_bounds (d := d) hd hlo hhi
  exact mul_le_mul_of_nonneg_right hlow (normalizedL2On_nonneg _ _)

/-- The reverse normalizer comparison, at the printed aspect ratio `3^{−2}`: the
general normalizer costs at most the factor `9`. -/
theorem oscillationOn_le_oscillationScaled_of_axisCubeSandwich (hd : d ≠ 0)
    {W : Set (Vec d)} {zin zout : Vec d} {j : ℤ}
    (hin : axisCube zin ((3 : ℝ) ^ (j - 2)) ⊆ W)
    (hout : W ⊆ axisCube zout ((3 : ℝ) ^ j)) (u : Vec d → ℝ) :
    oscillationOn W u ≤ 9 * oscillationScaled j W u := by
  obtain ⟨hlo, hhi⟩ := volume_toReal_bounds_of_axisCubeSandwich (d := d) hin hout
  obtain ⟨_, hhigh⟩ := rpow_normalizer_bounds (d := d) hd hlo hhi
  have h := mul_le_mul_of_nonneg_right hhigh (normalizedL2On_nonneg
    (W := W) (f := fun x => u x - volumeAverage W u))
  rw [oscillationOn, oscillationScaled]
  calc ((volume W).toReal) ^ (-(d : ℝ)⁻¹)
        * normalizedL2On W (fun x => u x - volumeAverage W u)
      ≤ 9 * (3 : ℝ) ^ (-j) * normalizedL2On W (fun x => u x - volumeAverage W u) := h
    _ = 9 * ((3 : ℝ) ^ (-j) * normalizedL2On W (fun x => u x - volumeAverage W u)) := by
        ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
