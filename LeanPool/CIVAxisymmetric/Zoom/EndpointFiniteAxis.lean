/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Analysis.BoundedAffine
public import LeanPool.CIVAxisymmetric.Statements.Dr
public import LeanPool.CIVAxisymmetric.Statements.Dz
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# The endpoint argument on the meridional half-plane

Let `V W : ℝ × ℝ → ℝ` be the radial and axial components of a divergence-free axisymmetric
meridional field on the closed half-plane `{R ≥ 0}`, of class `C¹` on the open half-plane
`{R > 0}` and with `V` bounded there.  Assume the two structural identities

* `∂_R V + V / R + ∂_Z W = 0` on `{R > 0}` (the divergence identity), and
* `∂_R W = 0` on `{R > 0}`.

Then `V` vanishes identically and both `∂_R V` and `∂_Z W` vanish identically.  The three steps
are the three theorems `endpoint_axial_const`, `endpoint_radial_eq` and
`endpoint_dz_axial_eq_zero`:

* `∂_R W = 0` on the connected half-line `{R > 0}` makes `W (R, Z)` independent of `R`, hence
  `∂_Z W (R, Z) = ∂_Z W (1, Z)` is a function `c Z` of `Z` alone;
* the divergence identity then reads `∂_R (R V) = −R · c Z`, so `R V (R, Z) + (R² / 2) · c Z` is
  constant in `R`; boundedness of `V` forces that constant to be `0`, i.e.
  `V (R, Z) = −(R / 2) · c Z`;
* boundedness of `V` on the *whole* half-line now forces `c Z = 0`, by
  `eq_zero_of_abs_mul_le_of_nonneg`.

Derivatives are taken in the form produced by `CIV.exists_subseq_tendstoUniformlyOn_c1`: a
Fréchet derivative `DV p : (ℝ × ℝ) →L[ℝ] ℝ` at `p : ℝ × ℝ`, whose radial and axial partial
derivatives are `DV p (1, 0)` and `DV p (0, 1)`.

The second half of the file transfers the conclusion to a `C¹`-convergent sequence: if
`DV n → DV⁰` uniformly on a set on which the limiting radial derivative vanishes, then
`∂_R V n → 0` uniformly there, and the radial quotients `V n / R` converge to `0` uniformly on
a segment `[0, A] × {Z}` of the closed half-plane, by the mean value theorem applied to
`R ↦ V n (R, Z)` on `[0, R]`.
-/

public section

open Set Filter Topology

noncomputable section
namespace CIV

/-! ### Elementary one-variable input -/

/-- A real function whose derivative vanishes on the open half-line `{x > 0}` is constant
there.  Proved from Lagrange's mean value theorem on `[u, v] ⊂ {x > 0}`. -/
private theorem eq_of_hasDerivAt_zero_pos {g : ℝ → ℝ}
    (hg : ∀ x : ℝ, 0 < x → HasDerivAt g 0 x) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    g a = g b := by
  have key : ∀ u v : ℝ, 0 < u → u < v → g u = g v := by
    intro u v hu huv
    have hcont : ContinuousOn g (Icc u v) := by
      intro x hx
      exact (hg x (lt_of_lt_of_le hu hx.1)).continuousAt.continuousWithinAt
    have hder : ∀ x ∈ Ioo u v, HasDerivAt g ((fun _ : ℝ => (0 : ℝ)) x) x := by
      intro x hx
      exact hg x (lt_trans hu hx.1)
    obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope g (fun _ : ℝ => (0 : ℝ)) huv hcont hder
    have hc' : (0 : ℝ) = (g v - g u) / (v - u) := hc
    have hvu : v - u ≠ 0 := sub_ne_zero.mpr (ne_of_gt huv)
    have hnum : g v - g u = 0 := (div_eq_zero_iff.mp hc'.symm).resolve_right hvu
    linarith only [hnum]
  rcases lt_trichotomy a b with h | h | h
  · exact key a b ha h
  · rw [h]
  · exact (key b a hb h).symm

/-! ### Reading partial derivatives off a Fréchet derivative -/

/-- The radial slice of a function with a Fréchet derivative at `(R, Z)` has derivative
`L (1, 0)` at `R`. -/
theorem hasDerivAt_radial_of_hasFDerivAt {f : ℝ × ℝ → ℝ} {L : (ℝ × ℝ) →L[ℝ] ℝ} {R Z : ℝ}
    (hf : HasFDerivAt f L (R, Z)) :
    HasDerivAt (fun r : ℝ => f (r, Z)) (L (1, 0)) R := by
  have hline : HasDerivAt (fun r : ℝ => (r, Z)) ((1 : ℝ), (0 : ℝ)) R :=
    (hasDerivAt_id R).prodMk (hasDerivAt_const R Z)
  exact hf.comp_hasDerivAt R hline

/-- The axial slice of a function with a Fréchet derivative at `(R, Z)` has derivative
`L (0, 1)` at `Z`. -/
theorem hasDerivAt_axial_of_hasFDerivAt {f : ℝ × ℝ → ℝ} {L : (ℝ × ℝ) →L[ℝ] ℝ} {R Z : ℝ}
    (hf : HasFDerivAt f L (R, Z)) :
    HasDerivAt (fun z : ℝ => f (R, z)) (L (0, 1)) Z := by
  have hline : HasDerivAt (fun z : ℝ => (R, z)) ((0 : ℝ), (1 : ℝ)) Z :=
    (hasDerivAt_const Z R).prodMk (hasDerivAt_id Z)
  exact hf.comp_hasDerivAt Z hline

/-- The repository's `dr` of a space-time field, at a fixed time, read off the Fréchet
derivative of the corresponding time slice. -/
theorem dr_eq_of_hasFDerivAt (phi : (ℝ × ℝ) × ℝ → ℝ) (t : ℝ) {L : (ℝ × ℝ) →L[ℝ] ℝ} {R Z : ℝ}
    (hphi : HasFDerivAt (fun p : ℝ × ℝ => phi (p, t)) L (R, Z)) :
    dr phi ((R, Z), t) = L (1, 0) := by
  have hd : HasDerivAt (fun r : ℝ => phi ((r, Z), t)) (L (1, 0)) R :=
    hasDerivAt_radial_of_hasFDerivAt (f := fun p : ℝ × ℝ => phi (p, t)) hphi
  change deriv (fun r : ℝ => phi ((r, Z), t)) R = L (1, 0)
  exact hd.deriv

/-- The repository's `dz` of a space-time field, at a fixed time, read off the Fréchet
derivative of the corresponding time slice. -/
theorem dz_eq_of_hasFDerivAt (phi : (ℝ × ℝ) × ℝ → ℝ) (t : ℝ) {L : (ℝ × ℝ) →L[ℝ] ℝ} {R Z : ℝ}
    (hphi : HasFDerivAt (fun p : ℝ × ℝ => phi (p, t)) L (R, Z)) :
    dz phi ((R, Z), t) = L (0, 1) := by
  have hd : HasDerivAt (fun z : ℝ => phi ((R, z), t)) (L (0, 1)) Z :=
    hasDerivAt_axial_of_hasFDerivAt (f := fun p : ℝ × ℝ => phi (p, t)) hphi
  change deriv (fun z : ℝ => phi ((R, z), t)) Z = L (0, 1)
  exact hd.deriv

/-! ### Step (a): the axial component does not depend on the radius -/

/-- If `∂_R W = 0` on the open half-plane, then `W (R, Z) = W (1, Z)` for every `R > 0`. -/
theorem endpoint_axial_const (W : ℝ × ℝ → ℝ) (DW : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hW : ∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt W (DW p) p)
    (hWr : ∀ p : ℝ × ℝ, 0 < p.1 → DW p (1, 0) = 0)
    (R Z : ℝ) (hR : 0 < R) :
    W (R, Z) = W (1, Z) := by
  refine eq_of_hasDerivAt_zero_pos (g := fun r : ℝ => W (r, Z)) ?_ hR one_pos
  intro x hx
  have hfd : HasFDerivAt W (DW (x, Z)) (x, Z) := hW (x, Z) hx
  have hd : HasDerivAt (fun r : ℝ => W (r, Z)) (DW (x, Z) (1, 0)) x :=
    hasDerivAt_radial_of_hasFDerivAt hfd
  have hzero : DW (x, Z) (1, 0) = 0 := hWr (x, Z) hx
  rw [hzero] at hd
  exact hd

/-- If `∂_R W = 0` on the open half-plane, then `∂_Z W (R, Z) = ∂_Z W (1, Z)` for every
`R > 0`: the axial derivative of `W` is a function of `Z` alone. -/
theorem endpoint_dz_axial_const (W : ℝ × ℝ → ℝ) (DW : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hW : ∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt W (DW p) p)
    (hWr : ∀ p : ℝ × ℝ, 0 < p.1 → DW p (1, 0) = 0)
    (R Z : ℝ) (hR : 0 < R) :
    DW (R, Z) (0, 1) = DW (1, Z) (0, 1) := by
  have hR' : HasDerivAt (fun z : ℝ => W (R, z)) (DW (R, Z) (0, 1)) Z :=
    hasDerivAt_axial_of_hasFDerivAt (hW (R, Z) hR)
  have h1 : HasDerivAt (fun z : ℝ => W (1, z)) (DW (1, Z) (0, 1)) Z :=
    hasDerivAt_axial_of_hasFDerivAt (hW ((1 : ℝ), Z) one_pos)
  have hfun : (fun z : ℝ => W (R, z)) = fun z : ℝ => W (1, z) := by
    funext z
    exact endpoint_axial_const W DW hW hWr R z hR
  rw [hfun] at hR'
  exact hR'.unique h1

/-! ### Step (b): the radial component is linear in the radius -/

/-- The divergence identity integrates from the axis: with `c Z := ∂_Z W (1, Z)` one has
`V (R, Z) = −(R / 2) · c Z` for every `R > 0`.  The integration constant is killed by the
boundedness of `V`, which makes `R · V (R, Z)` tend to `0` as `R → 0⁺`. -/
theorem endpoint_radial_eq (V W : ℝ × ℝ → ℝ) (DV DW : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)) (M : ℝ)
    (hV : ∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt V (DV p) p)
    (hW : ∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt W (DW p) p)
    (hbdd : ∀ p : ℝ × ℝ, 0 < p.1 → |V p| ≤ M)
    (hdiv : ∀ p : ℝ × ℝ, 0 < p.1 → DV p (1, 0) + V p / p.1 + DW p (0, 1) = 0)
    (hWr : ∀ p : ℝ × ℝ, 0 < p.1 → DW p (1, 0) = 0)
    (R Z : ℝ) (hR : 0 < R) :
    V (R, Z) = -(R / 2) * DW (1, Z) (0, 1) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, DW ((1 : ℝ), Z) (0, 1) = c := ⟨_, rfl⟩
  rw [hc]
  -- The auxiliary function `r ↦ r * V (r, Z) + (r ^ 2 / 2) * c` has vanishing derivative.
  have hgd : ∀ x : ℝ, 0 < x →
      HasDerivAt (fun r : ℝ => r * V (r, Z) + r ^ 2 / 2 * c) 0 x := by
    intro x hx
    have hVd : HasDerivAt (fun r : ℝ => V (r, Z)) (DV (x, Z) (1, 0)) x :=
      hasDerivAt_radial_of_hasFDerivAt (hV (x, Z) hx)
    have hlin : HasDerivAt (fun r : ℝ => r * V (r, Z))
        (1 * V (x, Z) + x * DV (x, Z) (1, 0)) x := (hasDerivAt_id' x).mul hVd
    have hsq : HasDerivAt (fun r : ℝ => r ^ 2) (2 * x) x := by
      have hp := hasDerivAt_pow 2 x
      simpa using hp
    have hquad : HasDerivAt (fun r : ℝ => r ^ 2 / 2 * c) (2 * x / 2 * c) x :=
      (hsq.div_const 2).mul_const c
    have hsum : HasDerivAt (fun r : ℝ => r * V (r, Z) + r ^ 2 / 2 * c)
        (1 * V (x, Z) + x * DV (x, Z) (1, 0) + 2 * x / 2 * c) x := hlin.add hquad
    have hdivx : DV (x, Z) (1, 0) + V (x, Z) / x + DW (x, Z) (0, 1) = 0 := hdiv (x, Z) hx
    have hdz : DW (x, Z) (0, 1) = c := by
      rw [endpoint_dz_axial_const W DW hW hWr x Z hx, hc]
    rw [hdz] at hdivx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hcancel : x * (V (x, Z) / x) = V (x, Z) := by field_simp
    have hscaled : x * DV (x, Z) (1, 0) + x * (V (x, Z) / x) + x * c = 0 := by
      linear_combination x * hdivx
    have hkey : x * DV (x, Z) (1, 0) = -V (x, Z) - x * c := by
      linarith only [hscaled, hcancel]
    have hval : 1 * V (x, Z) + x * DV (x, Z) (1, 0) + 2 * x / 2 * c = 0 := by
      linarith only [hkey]
    rw [hval] at hsum
    exact hsum
  -- Hence it is constant on the open half-line.
  have hconst : ∀ r : ℝ, 0 < r →
      r * V (r, Z) + r ^ 2 / 2 * c = 1 * V ((1 : ℝ), Z) + (1 : ℝ) ^ 2 / 2 * c := by
    intro r hr
    exact eq_of_hasDerivAt_zero_pos hgd hr one_pos
  obtain ⟨b, hb⟩ : ∃ b : ℝ, 1 * V ((1 : ℝ), Z) + (1 : ℝ) ^ 2 / 2 * c = b := ⟨_, rfl⟩
  -- The constant is `0`, because it is bounded by `r * M + (r ^ 2 / 2) * |c|` for every `r > 0`.
  have htend : Tendsto
      (fun n : ℕ => 1 / ((n : ℝ) + 1) * M + (1 / ((n : ℝ) + 1)) ^ 2 / 2 * |c|)
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 := (h0.mul_const M).add (((h0.pow 2).div_const 2).mul_const |c|)
    simpa using h1
  have hbound : ∀ n : ℕ,
      |b| ≤ 1 / ((n : ℝ) + 1) * M + (1 / ((n : ℝ) + 1)) ^ 2 / 2 * |c| := by
    intro n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hr : (0 : ℝ) < 1 / ((n : ℝ) + 1) := div_pos one_pos (by linarith only [hn0])
    have hcn := hconst (1 / ((n : ℝ) + 1)) hr
    rw [hb] at hcn
    have hsplit : |b| ≤ |1 / ((n : ℝ) + 1) * V (1 / ((n : ℝ) + 1), Z)|
        + |(1 / ((n : ℝ) + 1)) ^ 2 / 2 * c| := by
      rw [← hcn]
      exact abs_add_le _ _
    have h1 : |1 / ((n : ℝ) + 1) * V (1 / ((n : ℝ) + 1), Z)|
        = 1 / ((n : ℝ) + 1) * |V (1 / ((n : ℝ) + 1), Z)| := by
      rw [abs_mul, abs_of_pos hr]
    have hnn : (0 : ℝ) ≤ (1 / ((n : ℝ) + 1)) ^ 2 / 2 := by positivity
    have h2 : |(1 / ((n : ℝ) + 1)) ^ 2 / 2 * c| = (1 / ((n : ℝ) + 1)) ^ 2 / 2 * |c| := by
      rw [abs_mul, abs_of_nonneg hnn]
    have h3 : |V (1 / ((n : ℝ) + 1), Z)| ≤ M := hbdd (1 / ((n : ℝ) + 1), Z) hr
    have h4 : 1 / ((n : ℝ) + 1) * |V (1 / ((n : ℝ) + 1), Z)| ≤ 1 / ((n : ℝ) + 1) * M :=
      mul_le_mul_of_nonneg_left h3 hr.le
    linarith only [hsplit, h1, h2, h4]
  have hb0 : b = 0 := eq_zero_of_forall_abs_le_of_tendsto_zero htend hbound
  have hfinal : R * V (R, Z) + R ^ 2 / 2 * c = 0 := by
    have hcR := hconst R hR
    rw [hb, hb0] at hcR
    exact hcR
  have hRne : R ≠ 0 := ne_of_gt hR
  have hprod : R * (V (R, Z) - -(R / 2) * c) = 0 := by linear_combination hfinal
  rcases mul_eq_zero.mp hprod with h | h
  · exact absurd h hRne
  · linarith only [h]

/-! ### Step (c): boundedness forces the endpoint field to vanish -/

/-- Boundedness of `V` on the whole half-plane forces the `Z`-derivative of `W` to vanish. -/
theorem endpoint_dz_axial_eq_zero (V W : ℝ × ℝ → ℝ) (DV DW : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)) (M : ℝ)
    (hV : ∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt V (DV p) p)
    (hW : ∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt W (DW p) p)
    (hbdd : ∀ p : ℝ × ℝ, 0 < p.1 → |V p| ≤ M)
    (hdiv : ∀ p : ℝ × ℝ, 0 < p.1 → DV p (1, 0) + V p / p.1 + DW p (0, 1) = 0)
    (hWr : ∀ p : ℝ × ℝ, 0 < p.1 → DW p (1, 0) = 0)
    (Z : ℝ) :
    DW ((1 : ℝ), Z) (0, 1) = 0 := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hbdd ((1 : ℝ), Z) one_pos)
  have hhalf : DW ((1 : ℝ), Z) (0, 1) / 2 = 0 := by
    refine eq_zero_of_abs_mul_le_of_nonneg (M := M) ?_
    intro r hr
    rcases eq_or_lt_of_le hr with hr0 | hr0
    · rw [← hr0, zero_mul, abs_zero]
      exact hM
    · have heq := endpoint_radial_eq V W DV DW M hV hW hbdd hdiv hWr r Z hr0
      have hrw : r * (DW ((1 : ℝ), Z) (0, 1) / 2) = -V (r, Z) := by
        rw [heq]; ring
      rw [hrw, abs_neg]
      exact hbdd (r, Z) hr0
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  exact (div_eq_zero_iff.mp hhalf).resolve_right h2

/-- The radial component of the endpoint field vanishes on the open half-plane. -/
theorem endpoint_radial_eq_zero (V W : ℝ × ℝ → ℝ) (DV DW : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)) (M : ℝ)
    (hV : ∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt V (DV p) p)
    (hW : ∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt W (DW p) p)
    (hbdd : ∀ p : ℝ × ℝ, 0 < p.1 → |V p| ≤ M)
    (hdiv : ∀ p : ℝ × ℝ, 0 < p.1 → DV p (1, 0) + V p / p.1 + DW p (0, 1) = 0)
    (hWr : ∀ p : ℝ × ℝ, 0 < p.1 → DW p (1, 0) = 0)
    (p : ℝ × ℝ) (hp : 0 < p.1) :
    V p = 0 := by
  obtain ⟨R, Z⟩ := p
  have hR : 0 < R := hp
  have heq := endpoint_radial_eq V W DV DW M hV hW hbdd hdiv hWr R Z hR
  have hzero := endpoint_dz_axial_eq_zero V W DV DW M hV hW hbdd hdiv hWr Z
  rw [hzero, mul_zero] at heq
  exact heq

/-- The axial derivative of the axial component vanishes on the open half-plane. -/
theorem endpoint_dz_axial_eq_zero_of_pos (V W : ℝ × ℝ → ℝ)
    (DV DW : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)) (M : ℝ)
    (hV : ∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt V (DV p) p)
    (hW : ∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt W (DW p) p)
    (hbdd : ∀ p : ℝ × ℝ, 0 < p.1 → |V p| ≤ M)
    (hdiv : ∀ p : ℝ × ℝ, 0 < p.1 → DV p (1, 0) + V p / p.1 + DW p (0, 1) = 0)
    (hWr : ∀ p : ℝ × ℝ, 0 < p.1 → DW p (1, 0) = 0)
    (p : ℝ × ℝ) (hp : 0 < p.1) :
    DW p (0, 1) = 0 := by
  obtain ⟨R, Z⟩ := p
  have hR : 0 < R := hp
  rw [endpoint_dz_axial_const W DW hW hWr R Z hR]
  exact endpoint_dz_axial_eq_zero V W DV DW M hV hW hbdd hdiv hWr Z

/-- The radial derivative of the radial component vanishes on the open half-plane. -/
theorem endpoint_dr_radial_eq_zero (V W : ℝ × ℝ → ℝ) (DV DW : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)) (M : ℝ)
    (hV : ∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt V (DV p) p)
    (hW : ∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt W (DW p) p)
    (hbdd : ∀ p : ℝ × ℝ, 0 < p.1 → |V p| ≤ M)
    (hdiv : ∀ p : ℝ × ℝ, 0 < p.1 → DV p (1, 0) + V p / p.1 + DW p (0, 1) = 0)
    (hWr : ∀ p : ℝ × ℝ, 0 < p.1 → DW p (1, 0) = 0)
    (p : ℝ × ℝ) (hp : 0 < p.1) :
    DV p (1, 0) = 0 := by
  have hdivp := hdiv p hp
  have hVp : V p = 0 := endpoint_radial_eq_zero V W DV DW M hV hW hbdd hdiv hWr p hp
  have hWp : DW p (0, 1) = 0 :=
    endpoint_dz_axial_eq_zero_of_pos V W DV DW M hV hW hbdd hdiv hWr p hp
  rw [hVp, hWp, zero_div] at hdivp
  linarith only [hdivp]

/-- The full Fréchet derivative of the radial component vanishes on the open half-plane:
`V` is identically zero on the open set `{R > 0}`. -/
theorem endpoint_fderiv_radial_eq_zero (V W : ℝ × ℝ → ℝ)
    (DV DW : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)) (M : ℝ)
    (hV : ∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt V (DV p) p)
    (hW : ∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt W (DW p) p)
    (hbdd : ∀ p : ℝ × ℝ, 0 < p.1 → |V p| ≤ M)
    (hdiv : ∀ p : ℝ × ℝ, 0 < p.1 → DV p (1, 0) + V p / p.1 + DW p (0, 1) = 0)
    (hWr : ∀ p : ℝ × ℝ, 0 < p.1 → DW p (1, 0) = 0)
    (p : ℝ × ℝ) (hp : 0 < p.1) :
    DV p = 0 := by
  have hopen : IsOpen {q : ℝ × ℝ | 0 < q.1} := isOpen_lt continuous_const continuous_fst
  have hmem : {q : ℝ × ℝ | 0 < q.1} ∈ 𝓝 p := hopen.mem_nhds hp
  have hev : V =ᶠ[𝓝 p] fun _ : ℝ × ℝ => (0 : ℝ) := by
    filter_upwards [hmem] with q hq
    exact endpoint_radial_eq_zero V W DV DW M hV hW hbdd hdiv hWr q hq
  have hconst : HasFDerivAt (fun _ : ℝ × ℝ => (0 : ℝ)) (0 : (ℝ × ℝ) →L[ℝ] ℝ) p :=
    hasFDerivAt_const (0 : ℝ) p
  have hzero : HasFDerivAt V (0 : (ℝ × ℝ) →L[ℝ] ℝ) p := hconst.congr_of_eventuallyEq hev
  exact (hV p hp).unique hzero

/-- The endpoint conclusion, packaged: on the open half-plane the radial component, its radial
derivative, and the axial derivative of the axial component all vanish. -/
theorem endpoint_vanishing (V W : ℝ × ℝ → ℝ) (DV DW : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)) (M : ℝ)
    (hV : ∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt V (DV p) p)
    (hW : ∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt W (DW p) p)
    (hbdd : ∀ p : ℝ × ℝ, 0 < p.1 → |V p| ≤ M)
    (hdiv : ∀ p : ℝ × ℝ, 0 < p.1 → DV p (1, 0) + V p / p.1 + DW p (0, 1) = 0)
    (hWr : ∀ p : ℝ × ℝ, 0 < p.1 → DW p (1, 0) = 0) :
    (∀ p : ℝ × ℝ, 0 < p.1 → V p = 0) ∧ (∀ p : ℝ × ℝ, 0 < p.1 → DV p (1, 0) = 0) ∧
      (∀ p : ℝ × ℝ, 0 < p.1 → DW p (0, 1) = 0) :=
  ⟨fun p hp => endpoint_radial_eq_zero V W DV DW M hV hW hbdd hdiv hWr p hp,
    fun p hp => endpoint_dr_radial_eq_zero V W DV DW M hV hW hbdd hdiv hWr p hp,
    fun p hp => endpoint_dz_axial_eq_zero_of_pos V W DV DW M hV hW hbdd hdiv hWr p hp⟩

/-! ### Transfer to a `C¹`-convergent sequence -/

/-- Uniform convergence of continuous linear maps passes to their values at a fixed vector. -/
theorem tendstoUniformlyOn_clm_apply (S : Set (ℝ × ℝ))
    (D : ℕ → ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)) (D0 : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)) (v : ℝ × ℝ)
    (h : TendstoUniformlyOn D D0 atTop S) :
    TendstoUniformlyOn (fun n p => D n p v) (fun p => D0 p v) atTop S := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  have hv : (0 : ℝ) < ‖v‖ + 1 := by positivity
  filter_upwards [h (ε / (‖v‖ + 1)) (div_pos hε hv)] with n hn p hp
  have h1 := hn p hp
  have h2 : dist (D0 p v) (D n p v) ≤ dist (D0 p) (D n p) * ‖v‖ := by
    have hsub : (D0 p - D n p) v = D0 p v - D n p v := by simp
    have hle := ContinuousLinearMap.le_opNorm (D0 p - D n p) v
    rw [hsub] at hle
    rw [dist_eq_norm, dist_eq_norm]
    exact hle
  have hlt : ‖v‖ / (‖v‖ + 1) < 1 := by
    rw [div_lt_one hv]
    exact lt_add_one _
  have h4 : ε / (‖v‖ + 1) * ‖v‖ < ε := by
    calc ε / (‖v‖ + 1) * ‖v‖ = ε * (‖v‖ / (‖v‖ + 1)) := by ring
      _ < ε * 1 := mul_lt_mul_of_pos_left hlt hε
      _ = ε := mul_one ε
  calc dist (D0 p v) (D n p v) ≤ dist (D0 p) (D n p) * ‖v‖ := h2
    _ ≤ ε / (‖v‖ + 1) * ‖v‖ := mul_le_mul_of_nonneg_right h1.le (norm_nonneg v)
    _ < ε := h4

/-- If the limiting derivative annihilates `v` on `S`, the values at `v` converge uniformly
to `0` on `S`. -/
theorem tendstoUniformlyOn_clm_apply_zero (S : Set (ℝ × ℝ))
    (D : ℕ → ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)) (D0 : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)) (v : ℝ × ℝ)
    (h : TendstoUniformlyOn D D0 atTop S) (hzero : ∀ p ∈ S, D0 p v = 0) :
    TendstoUniformlyOn (fun n p => D n p v) (fun _ => (0 : ℝ)) atTop S :=
  (tendstoUniformlyOn_clm_apply S D D0 v h).congr_right fun p hp => hzero p hp

/-- A continuous function on `[0, A]` vanishing on `(0, A]` vanishes on all of `[0, A]`: the
value at the axis is recovered as a limit along `A / (n + 1)`. -/
theorem eq_zero_of_continuousOn_Icc_of_pos {f : ℝ → ℝ} {A : ℝ} (hA : 0 < A)
    (hcont : ContinuousOn f (Icc 0 A)) (hpos : ∀ r : ℝ, 0 < r → r ≤ A → f r = 0) :
    ∀ r ∈ Icc (0 : ℝ) A, f r = 0 := by
  have haxis : f 0 = 0 := by
    have hden : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := by
      intro n
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith only [hn0]
    have hpos' : ∀ n : ℕ, 0 < A / ((n : ℝ) + 1) := by
      intro n
      exact div_pos hA (by linarith only [hden n])
    have hle : ∀ n : ℕ, A / ((n : ℝ) + 1) ≤ A := fun n => div_le_self hA.le (hden n)
    have hmem : ∀ n : ℕ, A / ((n : ℝ) + 1) ∈ Icc (0 : ℝ) A :=
      fun n => ⟨(hpos' n).le, hle n⟩
    have htend : Tendsto (fun n : ℕ => A / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 := h0.const_mul A
      simpa [div_eq_mul_inv] using h1
    have hwithin : Tendsto (fun n : ℕ => A / ((n : ℝ) + 1)) atTop (𝓝[Icc (0 : ℝ) A] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ htend
        (Filter.Eventually.of_forall hmem)
    have hlim : Tendsto (fun n : ℕ => f (A / ((n : ℝ) + 1))) atTop (𝓝 (f 0)) :=
      (hcont 0 (left_mem_Icc.mpr hA.le)).tendsto.comp hwithin
    have hzero : (fun n : ℕ => f (A / ((n : ℝ) + 1))) = fun _ : ℕ => (0 : ℝ) :=
      funext fun n => hpos _ (hpos' n) (hle n)
    rw [hzero] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  intro r hr
  rcases eq_or_lt_of_le hr.1 with h0 | h0
  · rw [← h0]
    exact haxis
  · exact hpos r h0 hr.2

/-- Uniform convergence of the radial quotients `V n / R` to `0` on the segment
`[0, A] × {Z}` of the closed half-plane.  Each quotient is a value of the radial derivative at
an intermediate radius, by the mean value theorem applied to `r ↦ V n (r, Z)` on `[0, R]`; the
axis value `R = 0` is covered because `V n (0, Z) = 0`. -/
theorem tendstoUniformlyOn_radial_div (A Z : ℝ) (V : ℕ → ℝ × ℝ → ℝ)
    (DV : ℕ → ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (haxis : ∀ n : ℕ, V n (0, Z) = 0)
    (hcont : ∀ n : ℕ, ContinuousOn (fun r : ℝ => V n (r, Z)) (Icc 0 A))
    (hderiv : ∀ n : ℕ, ∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt (V n) (DV n p) p)
    (huniform : TendstoUniformlyOn (fun n p => DV n p (1, 0)) (fun _ => (0 : ℝ)) atTop
      (Icc (0 : ℝ) A ×ˢ ({Z} : Set ℝ))) :
    TendstoUniformlyOn (fun n p => V n p / p.1) (fun _ => (0 : ℝ)) atTop
      (Icc (0 : ℝ) A ×ˢ ({Z} : Set ℝ)) := by
  rw [Metric.tendstoUniformlyOn_iff] at huniform ⊢
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith only [hε]
  filter_upwards [huniform (ε / 2) hhalf] with n hn p hp
  obtain ⟨R, Y⟩ := p
  obtain ⟨hR, hY⟩ := hp
  have hYZ : Y = Z := hY
  subst hYZ
  have hR0 : (0 : ℝ) ≤ R := hR.1
  have hRA : R ≤ A := hR.2
  rcases eq_or_lt_of_le hR0 with h0 | h0
  · have hRzero : R = 0 := h0.symm
    have hdiv0 : V n (R, Y) / (R, Y).1 = 0 := by
      simp only [hRzero, div_zero]
    rw [hdiv0]
    simpa using hε
  · -- Mean value theorem on `[0, R]`.
    have hcontR : ContinuousOn (fun r : ℝ => V n (r, Y)) (Icc 0 R) :=
      (hcont n).mono (Icc_subset_Icc le_rfl hRA)
    have hderivR : ∀ x ∈ Ioo (0 : ℝ) R,
        HasDerivAt (fun r : ℝ => V n (r, Y)) ((fun x : ℝ => DV n (x, Y) (1, 0)) x) x := by
      intro x hx
      exact hasDerivAt_radial_of_hasFDerivAt (hderiv n (x, Y) hx.1)
    obtain ⟨c, hcmem, hceq⟩ := exists_hasDerivAt_eq_slope (fun r : ℝ => V n (r, Y))
      (fun x : ℝ => DV n (x, Y) (1, 0)) h0 hcontR hderivR
    have hslope : DV n (c, Y) (1, 0) = (V n (R, Y) - V n (0, Y)) / (R - 0) := hceq
    rw [haxis n, sub_zero, sub_zero] at hslope
    have hcS : (c, Y) ∈ Icc (0 : ℝ) A ×ˢ ({Y} : Set ℝ) :=
      ⟨⟨hcmem.1.le, le_trans hcmem.2.le hRA⟩, rfl⟩
    have hcbound := hn (c, Y) hcS
    have hcabs : |DV n (c, Y) (1, 0)| < ε / 2 := by
      have hd : dist ((0 : ℝ)) (DV n (c, Y) (1, 0)) < ε / 2 := hcbound
      rw [Real.dist_eq, zero_sub, abs_neg] at hd
      exact hd
    have hgoal : |V n (R, Y) / R| < ε / 2 := by
      rw [← hslope]
      exact hcabs
    have hdd : dist ((0 : ℝ)) (V n (R, Y) / (R, Y).1) < ε := by
      change dist ((0 : ℝ)) (V n (R, Y) / R) < ε
      rw [Real.dist_eq, zero_sub, abs_neg]
      linarith only [hgoal, hε]
    exact hdd

/-- The endpoint conclusion of Step 2 in uniform form on the segment `[0, A] × {Z}` of the
closed half-plane: along a sequence converging to the endpoint field in `C¹`, the radial
derivative of the radial component, the axial derivative of the axial component, and the
radial quotients all converge to `0` uniformly. -/
theorem endpoint_tendstoUniformlyOn_triple (A Z M : ℝ) (hA : 0 < A)
    (V W : ℝ × ℝ → ℝ) (DV DW : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (Vn : ℕ → ℝ × ℝ → ℝ) (DVn DWn : ℕ → ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hV : ∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt V (DV p) p)
    (hW : ∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt W (DW p) p)
    (hbdd : ∀ p : ℝ × ℝ, 0 < p.1 → |V p| ≤ M)
    (hdiv : ∀ p : ℝ × ℝ, 0 < p.1 → DV p (1, 0) + V p / p.1 + DW p (0, 1) = 0)
    (hWr : ∀ p : ℝ × ℝ, 0 < p.1 → DW p (1, 0) = 0)
    (hDVcont : ContinuousOn (fun r : ℝ => DV (r, Z) (1, 0)) (Icc 0 A))
    (hDWcont : ContinuousOn (fun r : ℝ => DW (r, Z) (0, 1)) (Icc 0 A))
    (hDVconv : TendstoUniformlyOn DVn DV atTop (Icc (0 : ℝ) A ×ˢ ({Z} : Set ℝ)))
    (hDWconv : TendstoUniformlyOn DWn DW atTop (Icc (0 : ℝ) A ×ˢ ({Z} : Set ℝ)))
    (haxis : ∀ n : ℕ, Vn n (0, Z) = 0)
    (hVncont : ∀ n : ℕ, ContinuousOn (fun r : ℝ => Vn n (r, Z)) (Icc 0 A))
    (hVnderiv : ∀ n : ℕ, ∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt (Vn n) (DVn n p) p) :
    TendstoUniformlyOn (fun n p => DVn n p (1, 0)) (fun _ => (0 : ℝ)) atTop
        (Icc (0 : ℝ) A ×ˢ ({Z} : Set ℝ)) ∧
      TendstoUniformlyOn (fun n p => DWn n p (0, 1)) (fun _ => (0 : ℝ)) atTop
        (Icc (0 : ℝ) A ×ˢ ({Z} : Set ℝ)) ∧
      TendstoUniformlyOn (fun n p => Vn n p / p.1) (fun _ => (0 : ℝ)) atTop
        (Icc (0 : ℝ) A ×ˢ ({Z} : Set ℝ)) := by
  have hDVaxis : ∀ r ∈ Icc (0 : ℝ) A, DV (r, Z) (1, 0) = 0 :=
    eq_zero_of_continuousOn_Icc_of_pos hA hDVcont
      (fun r hr _ => endpoint_dr_radial_eq_zero V W DV DW M hV hW hbdd hdiv hWr (r, Z) hr)
  have hDWaxis : ∀ r ∈ Icc (0 : ℝ) A, DW (r, Z) (0, 1) = 0 :=
    eq_zero_of_continuousOn_Icc_of_pos hA hDWcont
      (fun r hr _ => endpoint_dz_axial_eq_zero_of_pos V W DV DW M hV hW hbdd hdiv hWr (r, Z) hr)
  have hDVseg : ∀ p ∈ Icc (0 : ℝ) A ×ˢ ({Z} : Set ℝ), DV p (1, 0) = 0 := by
    rintro ⟨r, y⟩ ⟨hr, hy⟩
    have hyZ : y = Z := hy
    subst hyZ
    exact hDVaxis r hr
  have hDWseg : ∀ p ∈ Icc (0 : ℝ) A ×ˢ ({Z} : Set ℝ), DW p (0, 1) = 0 := by
    rintro ⟨r, y⟩ ⟨hr, hy⟩
    have hyZ : y = Z := hy
    subst hyZ
    exact hDWaxis r hr
  have hfirst : TendstoUniformlyOn (fun n p => DVn n p (1, 0)) (fun _ => (0 : ℝ)) atTop
      (Icc (0 : ℝ) A ×ˢ ({Z} : Set ℝ)) :=
    tendstoUniformlyOn_clm_apply_zero _ DVn DV (1, 0) hDVconv hDVseg
  refine ⟨hfirst, tendstoUniformlyOn_clm_apply_zero _ DWn DW (0, 1) hDWconv hDWseg, ?_⟩
  exact tendstoUniformlyOn_radial_div A Z Vn DVn haxis hVncont hVnderiv hfirst

end CIV
