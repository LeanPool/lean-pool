/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.SlopeStability

/-!
# SlopeStabilityEndpoints

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.ExcessDecay

open MeasureTheory
open HCPolySupport (Vec vecDot vecNormSq volumeAverage axisCube openCubeSet TriadicCube
  cubeScaleFactor)
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ### Small measure-theoretic helpers -/

private theorem volume_ne_top_of_toReal_pos {W : Set (Vec d)} (hW : 0 < (volume W).toReal) :
    volume W ≠ ⊤ := by
  intro htop
  rw [htop, ENNReal.toReal_top] at hW
  exact absurd hW (lt_irrefl 0)

/-- The volume average is additive on integrable differences. -/
theorem volumeAverage_sub_eq {V : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : IntegrableOn f V volume) (hg : IntegrableOn g V volume) :
    volumeAverage V (fun x => f x - g x) =
      volumeAverage V f - volumeAverage V g := by
  unfold volumeAverage
  rw [MeasureTheory.integral_sub hf hg]
  ring

private theorem volumeAverage_sub_of_integrable {W : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : IntegrableOn f W) (hg : IntegrableOn g W) :
    volumeAverage W (fun x => f x - g x) = volumeAverage W f - volumeAverage W g := by
  exact volumeAverage_sub_eq hf hg

/-- `‖a‖_{L²(W)} = |a|` for a constant `a`, on a window of positive finite volume. -/
theorem normalizedL2On_const_of_pos {W : Set (Vec d)} (hW : 0 < (volume W).toReal) (a : ℝ) :
    normalizedL2On W (fun _ => a) = |a| := by
  have h : volumeAverage W (fun _ : Vec d => a ^ 2) = a ^ 2 := volumeAverage_const_of_pos hW _
  rw [normalizedL2On, h, Real.sqrt_sq_eq_abs]

/-- **Jensen for the volume-normalized `L²` seminorm**: `|⨍_W f| ≤ ‖f‖_{L²(W)}`.

Obtained from the completed-square expansion `volumeAverage_sub_const_sq`: the average of
`(f − (f)_W)²` is `⨍f² − ((f)_W)²`, and it is nonnegative. -/
theorem abs_volumeAverage_le_normalizedL2On {W : Set (Vec d)} (hWm : MeasurableSet W)
    (hW : 0 < (volume W).toReal) {f : Vec d → ℝ} (hf : IntegrableOn f W)
    (hf2 : IntegrableOn (fun x => f x ^ 2) W) :
    |volumeAverage W f| ≤ normalizedL2On W f := by
  have hfin : volume W ≠ ⊤ := volume_ne_top_of_toReal_pos hW
  have hexp := volumeAverage_sub_const_sq hWm hW hfin hf hf2 (volumeAverage W f)
  have hnn : 0 ≤ volumeAverage W (fun x => (f x - volumeAverage W f) ^ 2) :=
    volumeAverage_sq_nonneg W (fun x => f x - volumeAverage W f)
  have hm2 : volumeAverage W f ^ 2 ≤ volumeAverage W (fun x => f x ^ 2) := by
    linarith only [hexp, hnn]
  rw [← Real.sqrt_sq_eq_abs, normalizedL2On]
  exact Real.sqrt_le_sqrt hm2

/-- Transfer the difference of nested-window means through normalized oscillation. -/
theorem abs_volumeAverage_sub_average_le {W V : Set (Vec d)}
    (hVm : MeasurableSet V) (hsub : V ⊆ W)
    (hWpos : 0 < (volume W).toReal) (hVpos : 0 < (volume V).toReal)
    (hVtop : volume V ≠ ⊤) {f : Vec d → ℝ} (hfV : IntegrableOn f V volume)
    (hfV2 : IntegrableOn (fun x => (f x - volumeAverage W f) ^ 2) V volume)
    (hfW2 : IntegrableOn (fun x => (f x - volumeAverage W f) ^ 2) W volume) :
    |volumeAverage V f - volumeAverage W f| ≤
      Real.sqrt ((volume W).toReal / (volume V).toReal) *
        normalizedL2On W (fun x => f x - volumeAverage W f) := by
  have : IsFiniteMeasure (volume.restrict V) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hVtop
  have hc : IntegrableOn (fun _ : Vec d => volumeAverage W f) V volume :=
    MeasureTheory.integrable_const _
  have hsubint : IntegrableOn (fun x => f x - volumeAverage W f) V volume := hfV.sub hc
  have hJ := abs_volumeAverage_le_normalizedL2On hVm hVpos hsubint hfV2
  rw [volumeAverage_sub_of_integrable hfV hc,
    volumeAverage_const_of_pos hVpos (volumeAverage W f)] at hJ
  exact hJ.trans (normalizedL2On_le_of_subset hsub hWpos hVpos hfW2)

/-! ### The oscillation -/

/-- The **volume-normalized oscillation** `osc(u,W) = |W|^{−1/d} ‖u −
(u)_W‖_{L²(W)}`: the `3^{−j}‖u − (u)_{U_j}‖_{L²(U_j)}` read at the
`e.excess.def` normalizer, so that it is directly comparable with
`affineExcess`. -/
def oscillationOn (W : Set (Vec d)) (u : Vec d → ℝ) : ℝ :=
  ((volume W).toReal) ^ (-(d : ℝ)⁻¹) * normalizedL2On W (fun x => u x - volumeAverage W u)

theorem oscillationOn_nonneg (W : Set (Vec d)) (u : Vec d → ℝ) : 0 ≤ oscillationOn W u :=
  mul_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) (normalizedL2On_nonneg _ _)

/-- The **scale-normalized oscillation** `3^{−j}‖u − (u)_W‖_{L²(W)}`: the literal
normalizer and of `e.excess.def.cubes`. -/
def oscillationScaled (j : ℤ) (W : Set (Vec d)) (u : Vec d → ℝ) : ℝ :=
  (3 : ℝ) ^ (-j) * normalizedL2On W (fun x => u x - volumeAverage W u)

theorem oscillationScaled_nonneg (j : ℤ) (W : Set (Vec d)) (u : Vec d → ℝ) :
    0 ≤ oscillationScaled j W u :=
  mul_nonneg (by positivity) (normalizedL2On_nonneg _ _)

/-- The un-normalized oscillation `‖u − (u)_W‖_{L²(W)} = |W|^{1/d} · osc(u,W)`. -/
theorem normalizedL2On_sub_average_eq {W : Set (Vec d)} (hW : 0 < (volume W).toReal)
    (u : Vec d → ℝ) :
    normalizedL2On W (fun x => u x - volumeAverage W u)
      = ((volume W).toReal) ^ ((d : ℝ)⁻¹) * oscillationOn W u := by
  have hne : ((volume W).toReal) ^ ((d : ℝ)⁻¹) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hW _)
  rw [oscillationOn, Real.rpow_neg hW.le, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

/-! ### The endpoint constant -/

/-- The **endpoint constant** of a sandwich of aspect ratio `θ`:
`Ci(θ) = 2 + K(θ) + 2/c₀(θ)`, a single constant dominating both endpoint comparisons.  Explicitly
a function of `(d, θ)`; no existential. -/
def endpointConst (d : ℕ) (θ : ℝ) : ℝ := 2 + oscConst d θ + 2 / ndConst d θ

theorem one_le_endpointConst {θ : ℝ} (hθ : 0 < θ) : (1 : ℝ) ≤ endpointConst d θ := by
  have hK : 0 < oscConst d θ := oscConst_pos hθ
  have hc : 0 < 2 / ndConst d θ := div_pos (by norm_num) (ndConst_pos hθ)
  rw [endpointConst]
  linarith only [hK, hc]

/-! ### `hhi`: the excess and the slope are controlled by the oscillation -/

/-- **`hhi` (the upper endpoint comparison), on a window carrying the inverse inequality.**
`E(u,W) + |∇ℓ| ≤ (1 + 2/c₀)·osc(u,W)` for an affine minimizer `(c,g)`.

`E ≤ osc` because the mean is one affine competitor; `|∇ℓ| ≤ (2/c₀)osc` because
`hnd` applied to `ℓ − (u)_W` plus Minkowski on `ℓ − (u)_W = (ℓ − u) + (u −
(u)_W)` give `c₀|W|^{1/d}|g| ≤ E_raw + osc_raw ≤ 2 osc_raw`.  `hnd` is the
inverse inequality, discharged from the sandwich in
`endpoint_comparisons_of_axisCubeSandwich`. -/
theorem affineExcess_add_slope_le_oscillationOn {W : Set (Vec d)} {u : Vec d → ℝ} {c : ℝ}
    {g : Vec d} (hW : 0 < (volume W).toReal) (hu : MemLp u 2 (volume.restrict W))
    (haff : ∀ (a : ℝ) (b : Vec d), MemLp (affineEval a b) 2 (volume.restrict W))
    (hmin : IsAffineMinimizer W u c g) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hnd : ∀ (a : ℝ) (b : Vec d),
      c₀ * ((volume W).toReal) ^ ((d : ℝ)⁻¹) * slopeMagnitude b
        ≤ normalizedL2On W (affineEval a b)) :
    affineExcess W u + slopeMagnitude g ≤ (1 + 2 / c₀) * oscillationOn W u := by
  have hfin : volume W ≠ ⊤ := volume_ne_top_of_toReal_pos hW
  have : IsFiniteMeasure (volume.restrict W) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hfin
  have hpos : (0 : ℝ) < ((volume W).toReal) ^ ((d : ℝ)⁻¹) := Real.rpow_pos_of_pos hW _
  -- the mean is an affine competitor: `E_raw ≤ osc_raw`.
  have ha : affineExcessRaw W u ≤ normalizedL2On W (fun x => u x - volumeAverage W u) :=
    affineExcessRaw_le_normalizedL2On_sub_const W u (volumeAverage W u)
  -- (b) the slope is controlled by `2 · osc_raw`.
  have hpt : affineEval (c - volumeAverage W u) g
      = fun x => (affineEval c g x - u x) + (u x - volumeAverage W u) := by
    funext x
    rw [affineEval, affineEval]
    ring
  have h1 : MemLp (fun x => affineEval c g x - u x) 2 (volume.restrict W) := (haff c g).sub hu
  have h2 : MemLp (fun x => u x - volumeAverage W u) 2 (volume.restrict W) :=
    hu.sub (memLp_const _)
  have hmink := normalizedL2On_add_le h1 h2
  have hsym : normalizedL2On W (fun x => affineEval c g x - u x) = affineExcessRaw W u := by
    rw [normalizedL2On_sub_comm W (affineEval c g) u]
    exact hmin
  have hb : c₀ * ((volume W).toReal) ^ ((d : ℝ)⁻¹) * slopeMagnitude g
      ≤ 2 * normalizedL2On W (fun x => u x - volumeAverage W u) := by
    have h := hnd (c - volumeAverage W u) g
    rw [hpt] at h
    rw [hsym] at hmink
    linarith only [h, hmink, ha]
  -- (c) restore the normalizers.
  have hosc := normalizedL2On_sub_average_eq hW u
  have hex := affineExcessRaw_eq_rpow_mul_affineExcess hW u
  have hE : affineExcess W u ≤ oscillationOn W u := by
    rw [hex, hosc] at ha
    exact le_of_mul_le_mul_left ha hpos
  have hS : slopeMagnitude g ≤ 2 / c₀ * oscillationOn W u := by
    rw [hosc] at hb
    have hb' : ((volume W).toReal) ^ ((d : ℝ)⁻¹) * (c₀ * slopeMagnitude g)
        ≤ ((volume W).toReal) ^ ((d : ℝ)⁻¹) * (2 * oscillationOn W u) := by
      linarith only [hb]
    have hb'' : c₀ * slopeMagnitude g ≤ 2 * oscillationOn W u :=
      le_of_mul_le_mul_left hb' hpos
    rw [div_mul_eq_mul_div, le_div_iff₀ hc₀]
    linarith only [hb'']
  linarith only [hE, hS]

/-! ### `hlo`: the oscillation is controlled by the excess and the slope -/

/-- **`hlo` (the lower endpoint comparison), on a window carrying the diameter inequality.**
`osc(u,W) ≤ (2 + K)(E(u,W) + |∇ℓ|)` for an affine minimizer `(c,g)`.

Triangle inequality on `u − (u)_W = (u − ℓ) + (ℓ − (ℓ)_W) + ((ℓ)_W − (u)_W)`;
the constant last term is `|⨍(ℓ − u)| ≤ ‖ℓ − u‖_{L²(W)} = E_raw` by Jensen.
`haffosc` is the direct (diameter) inequality, discharged from the sandwich in
`endpoint_comparisons_of_axisCubeSandwich`. -/
theorem oscillationOn_le_affineExcess_add_slope {W : Set (Vec d)} {u : Vec d → ℝ} {c : ℝ}
    {g : Vec d} (hWm : MeasurableSet W) (hW : 0 < (volume W).toReal)
    (hu : MemLp u 2 (volume.restrict W))
    (haff : ∀ (a : ℝ) (b : Vec d), MemLp (affineEval a b) 2 (volume.restrict W))
    (hmin : IsAffineMinimizer W u c g) {K : ℝ} (hK : 0 ≤ K)
    (haffosc : ∀ (a : ℝ) (b : Vec d),
      normalizedL2On W (fun x => affineEval a b x - volumeAverage W (affineEval a b))
        ≤ K * ((volume W).toReal) ^ ((d : ℝ)⁻¹) * slopeMagnitude b) :
    oscillationOn W u ≤ (2 + K) * (affineExcess W u + slopeMagnitude g) := by
  have hfin : volume W ≠ ⊤ := volume_ne_top_of_toReal_pos hW
  have : IsFiniteMeasure (volume.restrict W) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hfin
  have hpos : (0 : ℝ) < ((volume W).toReal) ^ ((d : ℝ)⁻¹) := Real.rpow_pos_of_pos hW _
  have huint : IntegrableOn u W := hu.integrable one_le_two
  have haint : IntegrableOn (affineEval c g) W := (haff c g).integrable one_le_two
  have hdiff : MemLp (fun x => affineEval c g x - u x) 2 (volume.restrict W) := (haff c g).sub hu
  have hdint : IntegrableOn (fun x => affineEval c g x - u x) W := hdiff.integrable one_le_two
  have hd2 : IntegrableOn (fun x => (affineEval c g x - u x) ^ 2) W :=
    (memLp_two_iff_integrable_sq hdiff.aestronglyMeasurable).1 hdiff
  have hsym : normalizedL2On W (fun x => affineEval c g x - u x) = affineExcessRaw W u := by
    rw [normalizedL2On_sub_comm W (affineEval c g) u]
    exact hmin
  -- the constant term `(ℓ)_W − (u)_W` is bounded by the excess, by Jensen.
  have hconst : |volumeAverage W (affineEval c g) - volumeAverage W u| ≤ affineExcessRaw W u := by
    have hsub := volumeAverage_sub_of_integrable (W := W) (f := affineEval c g) (g := u)
      haint huint
    have hj := abs_volumeAverage_le_normalizedL2On hWm hW hdint hd2
    rw [hsub, hsym] at hj
    exact hj
  -- the three-term triangle inequality.
  have hpt : (fun x => u x - volumeAverage W u)
      = fun x => (u x - affineEval c g x)
        + ((affineEval c g x - volumeAverage W (affineEval c g))
          + (volumeAverage W (affineEval c g) - volumeAverage W u)) := by
    funext x
    ring
  have h1 : MemLp (fun x => u x - affineEval c g x) 2 (volume.restrict W) := hu.sub (haff c g)
  have h2 : MemLp (fun x => affineEval c g x - volumeAverage W (affineEval c g)) 2
      (volume.restrict W) := (haff c g).sub (memLp_const _)
  have h3 : MemLp
      (fun _ : Vec d => volumeAverage W (affineEval c g) - volumeAverage W u) 2
      (volume.restrict W) := memLp_const _
  have h23 : MemLp (fun x => (affineEval c g x - volumeAverage W (affineEval c g))
      + (volumeAverage W (affineEval c g) - volumeAverage W u)) 2 (volume.restrict W) := h2.add h3
  have hmink1 := normalizedL2On_add_le (f := fun x => u x - affineEval c g x)
    (g := fun x => (affineEval c g x - volumeAverage W (affineEval c g))
      + (volumeAverage W (affineEval c g) - volumeAverage W u)) h1 h23
  have hmink2 := normalizedL2On_add_le
    (f := fun x => affineEval c g x - volumeAverage W (affineEval c g))
    (g := fun _ => volumeAverage W (affineEval c g) - volumeAverage W u) h2 h3
  have hc1 : normalizedL2On W
      (fun _ : Vec d => volumeAverage W (affineEval c g) - volumeAverage W u)
      = |volumeAverage W (affineEval c g) - volumeAverage W u| :=
    normalizedL2On_const_of_pos hW _
  have hc2 := haffosc c g
  have hc3 : normalizedL2On W (fun x => u x - affineEval c g x) = affineExcessRaw W u := hmin
  have hraw : normalizedL2On W (fun x => u x - volumeAverage W u)
      ≤ 2 * affineExcessRaw W u
        + K * ((volume W).toReal) ^ ((d : ℝ)⁻¹) * slopeMagnitude g := by
    rw [hpt]
    rw [hc1] at hmink2
    rw [hc3] at hmink1
    linarith only [hmink1, hmink2, hc2, hconst]
  -- restore the normalizers.
  have hosc := normalizedL2On_sub_average_eq hW u
  have hex := affineExcessRaw_eq_rpow_mul_affineExcess hW u
  rw [hosc, hex] at hraw
  have hstep : ((volume W).toReal) ^ ((d : ℝ)⁻¹) * oscillationOn W u
      ≤ ((volume W).toReal) ^ ((d : ℝ)⁻¹)
        * (2 * affineExcess W u + K * slopeMagnitude g) := by
    linarith only [hraw]
  have hfin2 : oscillationOn W u ≤ 2 * affineExcess W u + K * slopeMagnitude g :=
    le_of_mul_le_mul_left hstep hpos
  have hEnn : 0 ≤ affineExcess W u := affineExcess_nonneg _ _
  have hSnn : 0 ≤ slopeMagnitude g := slopeMagnitude_nonneg _
  have hKE : 0 ≤ K * affineExcess W u := mul_nonneg hK hEnn
  have hexp : (2 + K) * (affineExcess W u + slopeMagnitude g)
      = 2 * affineExcess W u + K * slopeMagnitude g
        + (2 * slopeMagnitude g + K * affineExcess W u) := by ring
  rw [hexp]
  linarith only [hfin2, hSnn, hKE]

/-! ### Both comparisons on a sandwiched window -/

/-- **The two endpoint comparisons on the sandwich class.**

On a window sandwiched between axis-parallel cubes of aspect ratio at least `θ`, with `(c,g)` a
chosen affine minimizer, both comparisons hold at the single explicit constant
`Ci = endpointConst d θ = 2 + K(θ) + 2/c₀(θ)`:

```
osc(u,W) ≤ Ci · (E(u,W) + |∇ℓ|)        and        E(u,W) + |∇ℓ| ≤ Ci · osc(u,W) .
```

Both halves of the affine window geometry are discharged from the sandwich: the
*inverse* inequality for the second, the *direct/diameter* inequality for the
first. -/
theorem endpoint_comparisons_of_axisCubeSandwich {W : Set (Vec d)} {zin zout : Vec d}
    {Lin Lout θ : ℝ} (hd : 0 < d) (hLin : 0 < Lin) (hLout : 0 < Lout) (hθ0 : 0 < θ)
    (hθ : θ * Lout ≤ Lin) (hWm : MeasurableSet W)
    (hin : axisCube zin Lin ⊆ W) (hout : W ⊆ axisCube zout Lout)
    {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict W)) {c : ℝ} {g : Vec d}
    (hmin : IsAffineMinimizer W u c g) :
    oscillationOn W u ≤ endpointConst d θ * (affineExcess W u + slopeMagnitude g)
      ∧ affineExcess W u + slopeMagnitude g ≤ endpointConst d θ * oscillationOn W u := by
  have hW : 0 < (volume W).toReal := volume_toReal_pos_of_sandwich hLin hin hout
  have haff : ∀ (a : ℝ) (b : Vec d), MemLp (affineEval a b) 2 (volume.restrict W) :=
    fun a b => memLp_affineEval_of_sandwich hLout hWm hout a b
  have hc₀ : 0 < ndConst d θ := ndConst_pos hθ0
  have hK : 0 < oscConst d θ := oscConst_pos hθ0
  have hnd : ∀ (a : ℝ) (b : Vec d),
      ndConst d θ * ((volume W).toReal) ^ ((d : ℝ)⁻¹) * slopeMagnitude b
        ≤ normalizedL2On W (affineEval a b) :=
    fun a b => normalizedL2On_affineEval_ge_of_sandwich hd hLin hLout hθ0 hθ hin hout a b
  have haffosc : ∀ (a : ℝ) (b : Vec d),
      normalizedL2On W (fun x => affineEval a b x - volumeAverage W (affineEval a b))
        ≤ oscConst d θ * ((volume W).toReal) ^ ((d : ℝ)⁻¹) * slopeMagnitude b :=
    fun a b => normalizedL2On_affineEval_sub_average_le_of_sandwich hd hLin hLout hθ0 hθ hWm
      hin hout a b
  have hlo := oscillationOn_le_affineExcess_add_slope hWm hW hu haff hmin hK.le haffosc
  have hhi := affineExcess_add_slope_le_oscillationOn hW hu haff hmin hc₀ hnd
  have hES : 0 ≤ affineExcess W u + slopeMagnitude g := by
    have h1 : 0 ≤ affineExcess W u := affineExcess_nonneg _ _
    have h2 : 0 ≤ slopeMagnitude g := slopeMagnitude_nonneg _
    linarith only [h1, h2]
  have hosc0 : 0 ≤ oscillationOn W u := oscillationOn_nonneg _ _
  have hinv : 0 < 2 / ndConst d θ := div_pos (by norm_num) hc₀
  refine ⟨hlo.trans ?_, hhi.trans ?_⟩
  · refine mul_le_mul_of_nonneg_right ?_ hES
    rw [endpointConst]
    linarith only [hinv]
  · refine mul_le_mul_of_nonneg_right ?_ hosc0
    rw [endpointConst]
    linarith only [hK]

/-! ### The `3^{−j}` normalizer -/

end

end Algsuperdiff.Section4.Provider.ExcessDecay
