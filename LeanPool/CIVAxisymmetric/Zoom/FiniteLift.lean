/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.FiniteAxisBounds
public import LeanPool.CIVAxisymmetric.Zoom.ChainRuleSecond
public import LeanPool.CIVAxisymmetric.Identities.ForceQuotient
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The finite-axis lift: regularity across `X = 0`, the lifted scalar, the force limit

Three of the four remaining pieces of the anisotropic zoom-in lift of `eq:drift:Bn:def`.

* The regularity of the lifted drift `B_n` across the axis `X = 0`. The Jacobian bound
  `norm_zoomDriftJacobian_le` is off-axis only (`0 < zoomLiftRadius`), since `zoomLiftRadius`
  itself has a cone singularity at `X = 0` and is not differentiable there. The honest question
  is not about `zoomLiftRadius`, but about `B_n`'s own radial part
  `V_n(|X|, Z, τ) X/|X|`. Along every ray through the axis in a single lifted radial
  coordinate, this part is *exactly* `V_n` itself — not merely close to it — because `V_n`,
  regarded as a function of the signed Cartesian radial coordinate, is odd
  (`apply_meridional_reflect_zero`), and the odd reflection of a function through the origin is
  exactly what the direction cosine `X/|X|` builds back out of `|X|`. This gives a genuine
  two-sided derivative of `B_n`'s ray restriction *at* the axis, equal to the derivative of
  `V_n` there (`hasDerivAt_zoomDrift_diag_ray_zero`), together with a quantitative bound of the
  radial part by `C |τ|^{-1/2}` times the distance to the axis
  (`abs_zoomDrift_apply_le_mul_zoomLiftRadius`), which is Lipschitz regularity. What is *not*
  established, and is not claimed, is joint (Fréchet) differentiability of the full map
  `X ↦ B_n(X, Z, τ)` at `X = 0`: that would need `V_n(\cdot, Z, τ)` to be a smooth function of
  the square of the radius, a structural fact beyond the pointwise derivative bounds proved in
  `CIV.Zoom.FiniteAxisBounds`.
* The force term `G_n` of `eq:interior:force:scaled` obeys `|G_n| ≤ C λ^5 λ^{2h}`, and this
  bound tends to zero as `λ → 0⁺`, the limit taken in the zoom scale.
* The lifted potential vorticity `Ω_tilde(X, Z, τ) = Ω_n(|X|, Z, τ)` of the paragraph before
  `eq:aniso:zoom:lifted`, and its finite-axis bound, transported through the lift.

The lifted equation `eq:aniso:zoom:lifted` itself is stated off the axis in
`CIV.Zoom.FiniteLiftEquation`, where the radial operator `∂_RR + 3R⁻¹∂_R` is identified with the
Laplacian `Δ_X` of the four lifted spatial coordinates. No finite-`n` equation is stated across
the axis: the limit equation `eq:aniso:zoom:finite:limit`, in the form
`IsDistributionalDriftDiffusion` that `lem:aniso:comparison` uses, is obtained with a cutoff at
the axis (deviation D17).
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-! ### (a) The regularity of the lifted drift across the axis -/

/-- `V_n` is odd under reflection of its radial argument: the underlying Cartesian velocity
component `u_1` is odd across the meridional reflection `x_1 ↦ -x_1`
(`apply_meridional_reflect_zero`), and `zoomV` is `u_1` composed with the affine zoom-in map. -/
theorem zoomV_odd (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (haxi : IsAxisymmetricOn u unitCylinder) {r Z τ : ℝ}
    (hp : zoomPoint lam h zc ((r, Z), τ) ∈ unitCylinder) :
    zoomV lam h zc u ((-r, Z), τ) = -zoomV lam h zc u ((r, Z), τ) := by
  have key := apply_meridional_reflect_zero haxi hp
  have hneg : lam * -r = -(lam * r) := by ring
  unfold zoomV zoomPoint
  simp only [hneg]
  rw [key]
  ring

/-- The point of `Vec 5` on the axis at height `Z`: the four radial coordinates vanish, and
the fifth (vertical) coordinate is `Z`. -/
@[expose] def zoomAxisPoint (Z : ℝ) : Vec 5 := Function.update (0 : Vec 5) 4 Z

theorem zoomAxisPoint_apply_four (Z : ℝ) : zoomAxisPoint Z 4 = Z := by
  unfold zoomAxisPoint
  rw [Function.update_self]

/-- Updating `zoomAxisPoint Z` at a single radial coordinate `i` gives a point whose lifted
radius is `|s|`, since the other three radial coordinates still vanish. -/
private theorem zoomLiftRadius_update_zoomAxisPoint {i : Fin 5} (hi : i ≠ 4) (Z s : ℝ) :
    zoomLiftRadius (Function.update (zoomAxisPoint Z) i s) = |s| := by
  fin_cases i
  · simp only [zoomLiftRadius, zoomAxisPoint, Function.update_apply]
    norm_num [Real.sqrt_sq_eq_abs]
  · simp only [zoomLiftRadius, zoomAxisPoint, Function.update_apply]
    norm_num [Real.sqrt_sq_eq_abs]
  · simp only [zoomLiftRadius, zoomAxisPoint, Function.update_apply]
    norm_num [Real.sqrt_sq_eq_abs]
  · simp only [zoomLiftRadius, zoomAxisPoint, Function.update_apply]
    norm_num [Real.sqrt_sq_eq_abs]
  · exact absurd rfl hi

/-- The lifted point of the ray through the axis at coordinate `i` and height `Z` is
`(|s|, Z, τ)`: the lifted radius is `|s|` (`zoomLiftRadius_update_zoomAxisPoint`), and the
vertical coordinate is untouched by the update since `i ≠ 4`. -/
private theorem zoomLiftPoint_update_zoomAxisPoint {i : Fin 5} (hi : i ≠ 4) (Z s τ : ℝ) :
    zoomLiftPoint (Function.update (zoomAxisPoint Z) i s, τ) = ((|s|, Z), τ) := by
  simp only [zoomLiftPoint, zoomLiftRadius_update_zoomAxisPoint hi Z s,
    Function.update_of_ne (Ne.symm hi) s (zoomAxisPoint Z), zoomAxisPoint_apply_four]

/-- The exact regularity across the axis: along any ray through the axis in a single lifted
radial coordinate `i`, the diagonal (matching) radial component of the lifted drift `B_n`
*equals* `V_n` itself, for every real `s` — not merely close to it. This is the honest
statement in place of smoothness of `zoomLiftRadius`, which has a cone singularity at `s = 0`:
the singularity of `X ↦ X/|X|` there is exactly cancelled by the fact that `V_n`, as a function
of the *signed* Cartesian radial coordinate, is odd (`zoomV_odd`), so `V_n(|s|, Z, τ) · s/|s|`
collapses to `V_n(s, Z, τ)` on both sides of `s = 0`, and to `0` (by `zoomV_axis`) at `s = 0`
itself. -/
theorem zoomDrift_diag_ray_eq (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (haxi : IsAxisymmetricOn u unitCylinder) {i : Fin 5} (hi : i ≠ 4) {Z s τ : ℝ}
    (hp : zoomPoint lam h zc ((|s|, Z), τ) ∈ unitCylinder) :
    zoomDrift lam h zc u (Function.update (zoomAxisPoint Z) i s, τ) i
      = zoomV lam h zc u ((s, Z), τ) := by
  have hlift := zoomLiftPoint_update_zoomAxisPoint hi Z s τ
  have hcoord : Function.update (zoomAxisPoint Z) i s i = s :=
    Function.update_self i s (zoomAxisPoint Z)
  simp only [zoomDrift]
  split_ifs with hcase
  · exact absurd hcase hi
  · simp only [hlift, hcoord, zoomLiftRadius_update_zoomAxisPoint hi Z s]
    rcases lt_trichotomy s 0 with hs | hs | hs
    · have hodd := zoomV_odd lam h zc u haxi (r := -s) (Z := Z) (τ := τ)
        (by rwa [abs_of_neg hs] at hp)
      rw [neg_neg] at hodd
      have hratio : s / (-s) = -1 := by
        rw [div_neg, div_self (ne_of_lt hs)]
      rw [abs_of_neg hs, hratio, mul_neg_one]
      linarith only [hodd]
    · subst hs
      simp only [abs_zero]
      have hz0 : zoomV lam h zc u ((0, Z), τ) = 0 := zoomV_axis lam h zc u haxi (by simpa using hp)
      rw [hz0]
      ring
    · rw [abs_of_pos hs, div_self (ne_of_gt hs), mul_one]

/-- Genuine two-sided differentiability of `B_n`'s diagonal ray-restriction *at the crossing*
`s = 0`: `zoomDrift_diag_ray_eq` identifies the ray-restriction with `V_n` on a whole
neighbourhood of `s = 0` (not merely pointwise), so its derivative at the crossing exists and
equals the derivative of `V_n` there, already available off the axis. This is the sharpest
statement available: it does *not* extend to a joint (Fréchet) derivative of the full map
`X ↦ B_n(X, Z, τ)` at `X = 0` in every direction at once, which would need `V_n(\cdot, Z, τ)`
to depend smoothly on the *square* of its argument — a structural fact beyond the pointwise
derivative bounds proved in `CIV.Zoom.FiniteAxisBounds`. -/
theorem hasDerivAt_zoomDrift_diag_ray_zero (lam h zc : ℝ) (u : ParabolicPoint → Vec3)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {i : Fin 5} (hi : i ≠ 4) {Z τ : ℝ}
    (hp : zoomPoint lam h zc ((0, Z), τ) ∈ unitCylinder) :
    HasDerivAt (fun s : ℝ => zoomDrift lam h zc u (Function.update (zoomAxisPoint Z) i s, τ) i)
      (dr (zoomV lam h zc u) ((0, Z), τ)) 0 := by
  have hbase := hasDerivAt_zoomV_radial lam h zc u hu ((0, Z), τ) hp
  refine hbase.congr_of_eventuallyEq ?_
  have hS_open : IsOpen {r : ℝ | zoomPoint lam h zc ((r, Z), τ) ∈ unitCylinder} :=
    isOpen_slice_r lam h zc ((0, Z), τ)
  have hS' : IsOpen ({r : ℝ | zoomPoint lam h zc ((r, Z), τ) ∈ unitCylinder}
      ∩ (Neg.neg ⁻¹' {r : ℝ | zoomPoint lam h zc ((r, Z), τ) ∈ unitCylinder})) :=
    hS_open.inter (hS_open.preimage continuous_neg)
  have h0S' : (0 : ℝ) ∈ {r : ℝ | zoomPoint lam h zc ((r, Z), τ) ∈ unitCylinder}
      ∩ (Neg.neg ⁻¹' {r : ℝ | zoomPoint lam h zc ((r, Z), τ) ∈ unitCylinder}) := by
    refine ⟨hp, ?_⟩
    change zoomPoint lam h zc ((-(0:ℝ), Z), τ) ∈ unitCylinder
    simpa using hp
  filter_upwards [hS'.mem_nhds h0S'] with s hs
  have hmem : zoomPoint lam h zc ((|s|, Z), τ) ∈ unitCylinder := by
    rcases le_total (0:ℝ) s with hs0 | hs0
    · rw [abs_of_nonneg hs0]
      exact hs.1
    · rw [abs_of_nonpos hs0]
      exact hs.2
  exact zoomDrift_diag_ray_eq lam h zc u haxi hi hmem

/-- The quantitative Lipschitz-to-axis bound: every radial component of the lifted drift `B_n`
is within `C |τ|^{-1/2}` times the distance to the axis, in every direction at once (not just
along coordinate rays) — this is the genuine, general-purpose "Lipschitz across `X = 0`"
content of the footnote to `eq:drift:Bn:def`. It follows from the same segment bound
`abs_zoomV_div_le` that supplies the diagonal entry of `norm_zoomDriftJacobian_le`, combined
with the direction-cosine bound `abs_le_zoomLiftRadius`; it holds at the axis itself, where
both sides vanish. -/
theorem abs_zoomDrift_apply_le_mul_zoomLiftRadius {C h lam zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {q : Vec 5 × ℝ}
    (hp : zoomPoint lam h zc (zoomLiftPoint q) ∈ unitCylinder) (hC : 0 ≤ C) (hτ : q.2 ≤ -1)
    {i : Fin 5} (hi : i ≠ 4) :
    |zoomDrift lam h zc u q i| ≤ C * (-q.2) ^ (-(1 / 2 : ℝ)) * zoomLiftRadius q.1 := by
  rcases eq_or_ne (zoomLiftRadius q.1) 0 with hR0 | hR0
  · rw [zoomDrift_apply_axis lam h zc u hR0 hi, hR0]
    simp
  · have hR : 0 < zoomLiftRadius q.1 :=
      (zoomLiftRadius_nonneg q.1).lt_of_ne (Ne.symm hR0)
    have hVdiv := abs_zoomV_div_le hlam hb hu haxi hp hR0 hC hτ
    have hXi := abs_le_zoomLiftRadius q.1 hi
    have heq : zoomV lam h zc u (zoomLiftPoint q) * (q.1 i / zoomLiftRadius q.1)
        = (zoomV lam h zc u (zoomLiftPoint q) / zoomLiftRadius q.1) * q.1 i := by
      field_simp
    simp only [zoomDrift]
    split_ifs with hcase
    · exact absurd hcase hi
    · rw [heq, abs_mul]
      have hbound : (0:ℝ) ≤ C * (-q.2) ^ (-(1 / 2 : ℝ)) :=
        mul_nonneg hC (Real.rpow_nonneg (by linarith only [hτ]) _)
      calc |zoomV lam h zc u (zoomLiftPoint q) / zoomLiftRadius q.1| * |q.1 i|
          ≤ C * (-q.2) ^ (-(1 / 2 : ℝ)) * zoomLiftRadius q.1 :=
            mul_le_mul hVdiv hXi (abs_nonneg _) hbound

/-! ### (d) The force term vanishes in the zoom scale -/

/-- The rescaled force term `G_n` of `eq:interior:force:scaled`: `λ^5 λ^{2h}` times the
potential vorticity of the force, evaluated at the zoom point — the force term of
`eq:aniso:zoom:finite:equation`, exactly as it enters `zoomOmega_pde`. -/
@[expose] def zoomForce (lam h zc : ℝ) (f : ParabolicPoint → Vec3) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  lam ^ 5 * lam ^ (2 * h) * potentialVorticity f (zoomPoint lam h zc p)

/-- `|G_n| ≤ C λ^5 λ^{2h}` on the preimage of the unit cylinder, uniformly in the point: the
potential vorticity of a `C²`-bounded, axisymmetric, `C^∞` force is bounded by a constant
depending only on the force (`abs_potentialVorticity_force_le`), and `λ^5 λ^{2h} ≥ 0` for
`λ > 0`. -/
theorem abs_zoomForce_le {lam h zc : ℝ} (hlam : 0 < lam) {f : ParabolicPoint → Vec3}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hfaxi : IsAxisymmetricOn f unitCylinder) (hMf : ForceC2Bounded f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : (ℝ × ℝ) × ℝ, zoomPoint lam h zc p ∈ unitCylinder →
      |zoomForce lam h zc f p| ≤ C * (lam ^ 5 * lam ^ (2 * h)) := by
  obtain ⟨C, hC, hCbound⟩ := abs_potentialVorticity_force_le hf hfaxi hMf
  refine ⟨C, hC, fun p hp => ?_⟩
  have hpv : |potentialVorticity f (zoomPoint lam h zc p)| ≤ C := hCbound _ _ _ hp
  have hpos : (0:ℝ) ≤ lam ^ 5 * lam ^ (2 * h) := by positivity
  rw [zoomForce, abs_mul, abs_of_nonneg hpos]
  calc lam ^ 5 * lam ^ (2 * h) * |potentialVorticity f (zoomPoint lam h zc p)|
      ≤ lam ^ 5 * lam ^ (2 * h) * C := mul_le_mul_of_nonneg_left hpv hpos
    _ = C * (lam ^ 5 * lam ^ (2 * h)) := by ring

/-- The bound of `abs_zoomForce_le` tends to zero in the zoom scale, as `λ → 0⁺`: this is
`|G_n| ≤ C M_f λ^5 δ_n → 0`, the fourth of the missing pieces, since `λ^5 λ^{2h} = λ^{5 + 2h}`
and `5 + 2h > 0`. -/
theorem tendsto_zoomForce_bound_nhdsWithin_zero {C h : ℝ} (hh0 : 0 ≤ h) :
    Filter.Tendsto (fun lam : ℝ => C * (lam ^ 5 * lam ^ (2 * h)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hcongr : Set.EqOn (fun lam : ℝ => C * (lam ^ 5 * lam ^ (2 * h)))
      (fun lam : ℝ => C * lam ^ (5 + 2 * h)) (Set.Ioi (0:ℝ)) := by
    intro lam hlam
    have hlam0 : (0:ℝ) < lam := hlam
    simp only
    rw [Real.rpow_add hlam0]
    norm_num [Real.rpow_natCast]
  rw [Filter.tendsto_congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin hcongr)]
  have hexp : (0:ℝ) < 5 + 2 * h := by linarith only [hh0]
  have hcont : ContinuousAt (fun lam : ℝ => C * lam ^ (5 + 2 * h)) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 (5 + 2 * h) (Or.inr hexp.le))
  have hzero : (0:ℝ) ^ (5 + 2 * h) = 0 := Real.zero_rpow (ne_of_gt hexp)
  have := hcont.tendsto
  rw [hzero, mul_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-! ### (b) The lifted scalar `Ω_tilde` -/

/-- The lifted potential vorticity `Ω_tilde(X, Z, τ) = Ω_n(|X|, Z, τ)` of the paragraph before
`eq:aniso:zoom:lifted`: `zoomOmega` composed with the lift `zoomLiftPoint`, a function of the
lifted spatial point `(X, Z) ∈ Vec 5` and the rescaled time `τ`. -/
@[expose] def zoomOmegaLift (lam h zc : ℝ) (u : ParabolicPoint → Vec3) (q : Vec 5 × ℝ) : ℝ :=
  zoomOmega lam h zc u (zoomLiftPoint q)

/-- The finite-axis bound `eq:aniso:zoom:finite:bound` for the lifted scalar, on and off the
axis: `abs_zoomOmega_le_of_mem` transported through the lift. -/
theorem abs_zoomOmegaLift_le {C h lam zc : ℝ} (hlam : 0 < lam) {u : ParabolicPoint → Vec3}
    (hb : AnisotropicBounds C h u) (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {q : Vec 5 × ℝ}
    (hp : zoomPoint lam h zc (zoomLiftPoint q) ∈ unitCylinder) :
    |zoomOmegaLift lam h zc u q|
      ≤ C * ((lam ^ (2 * h)) ^ 2 * (-q.2) ^ (-(3 / 2 : ℝ) + h)
          + (-q.2) ^ (-(3 / 2 : ℝ) - h)) :=
  abs_zoomOmega_le_of_mem hlam hb hu haxi hp

/-- The uniform-in-`n` bound `2C` for `τ ≤ -1`, the form the compactness argument of
`eq:aniso:zoom:finite:compactness` actually uses: `abs_zoomOmega_le_two_mul_const` transported
through the lift. -/
theorem abs_zoomOmegaLift_le_two_mul_const {C h lam zc : ℝ} (hlam : 0 < lam)
    {u : ParabolicPoint → Vec3} (hb : AnisotropicBounds C h u)
    (hu : ContDiffOn ℝ 2 (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) {q : Vec 5 × ℝ}
    (hp : zoomPoint lam h zc (zoomLiftPoint q) ∈ unitCylinder) (hC : 0 ≤ C)
    (hδ : lam ^ (2 * h) ≤ 1) (hh0 : 0 < h) (hh1 : h < 1 / 2) (hτ : q.2 ≤ -1) :
    |zoomOmegaLift lam h zc u q| ≤ 2 * C :=
  abs_zoomOmega_le_two_mul_const hlam hb hu haxi hp hC hδ hh0 hh1 hτ

end CIV
