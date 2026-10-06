/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.EndpointFiniteAxis
public import LeanPool.CIVAxisymmetric.Analysis.BoundedAffine

/-!
# The receding-axis endpoint argument

Step 3 of Section 4: the algebraic core of `eq:aniso:zoom:receding:limit`'s time-`τ = −1` slice.
On the whole meridional half-plane lifted to `ℝ × ℝ` (no axis restriction, unlike the
finite-axis case of `CIV/Zoom/EndpointFiniteAxis.lean`, whose divergence identity carries a
`V / R` term), a divergence-free pair `(V, W)` with `∂_R W = 0` and `V` bounded has `W`
independent of `R` and, once boundedness is used, both `∂_R V` and `∂_Z W` vanish identically —
the receding-axis analogue of `CIV.endpoint_vanishing`.
-/

public section

open Set Filter Topology

noncomputable section
namespace CIV



theorem endpoint_axial_const_rec (W : ℝ × ℝ → ℝ) (DW : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hW : ∀ p : ℝ × ℝ, HasFDerivAt W (DW p) p)
    (hWr : ∀ p : ℝ × ℝ, DW p (1, 0) = 0)
    (R Z : ℝ) :
    W (R, Z) = W (0, Z) := by
  set g := fun r : ℝ => W (r, Z) with hg
  have hg_diff : Differentiable ℝ g := by
    intro r
    have hfd : HasFDerivAt W (DW (r, Z)) (r, Z) := hW (r, Z)
    have hderiv : HasDerivAt g (DW (r, Z) (1, 0)) r :=
      hasDerivAt_radial_of_hasFDerivAt hfd
    have hzero : DW (r, Z) (1, 0) = 0 := hWr (r, Z)
    rw [hzero] at hderiv
    exact hderiv.differentiableAt
  have hg_fderiv : ∀ r : ℝ, fderiv ℝ g r = 0 := by
    intro r
    have hfd : HasFDerivAt W (DW (r, Z)) (r, Z) := hW (r, Z)
    have hderiv : HasDerivAt g (DW (r, Z) (1, 0)) r :=
      hasDerivAt_radial_of_hasFDerivAt hfd
    have hzero : DW (r, Z) (1, 0) = 0 := hWr (r, Z)
    rw [hzero] at hderiv
    have hfderiv : HasFDerivAt g (0 : ℝ →L[ℝ] ℝ) r := by
      simpa using hderiv.hasFDerivAt
    exact hfderiv.fderiv
  exact is_const_of_fderiv_eq_zero hg_diff hg_fderiv R 0

theorem endpoint_dz_axial_const_rec (W : ℝ × ℝ → ℝ) (DW : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hW : ∀ p : ℝ × ℝ, HasFDerivAt W (DW p) p)
    (hWr : ∀ p : ℝ × ℝ, DW p (1, 0) = 0)
    (R Z : ℝ) :
    DW (R, Z) (0, 1) = DW (0, Z) (0, 1) := by
  have hfun : (fun z : ℝ => W (R, z)) = (fun z : ℝ => W (0, z)) := by
    funext z
    exact endpoint_axial_const_rec W DW hW hWr R z
  have hRderiv : HasDerivAt (fun z : ℝ => W (R, z)) (DW (R, Z) (0, 1)) Z :=
    hasDerivAt_axial_of_hasFDerivAt (hW (R, Z))
  have h0deriv : HasDerivAt (fun z : ℝ => W (0, z)) (DW (0, Z) (0, 1)) Z :=
    hasDerivAt_axial_of_hasFDerivAt (hW (0, Z))
  rw [hfun] at hRderiv
  exact hRderiv.unique h0deriv

theorem endpoint_radial_eq_rec (V W : ℝ × ℝ → ℝ) (DV DW : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hV : ∀ p : ℝ × ℝ, HasFDerivAt V (DV p) p)
    (hW : ∀ p : ℝ × ℝ, HasFDerivAt W (DW p) p)
    (hdiv : ∀ p : ℝ × ℝ, DV p (1, 0) + DW p (0, 1) = 0)
    (hWr : ∀ p : ℝ × ℝ, DW p (1, 0) = 0)
    (R Z : ℝ) :
    V (R, Z) = V (0, Z) - R * DW (0, Z) (0, 1) := by
  set g := fun r : ℝ => V (r, Z) + r * DW (0, Z) (0, 1) with hg
  have hg_diff : Differentiable ℝ g := by
    intro r
    have hVderiv : HasDerivAt (fun r' : ℝ => V (r', Z)) (DV (r, Z) (1, 0)) r :=
      hasDerivAt_radial_of_hasFDerivAt (hV (r, Z))
    have hlinear : HasDerivAt (fun r' : ℝ => r' * DW (0, Z) (0, 1))
        (1 * DW (0, Z) (0, 1)) r := by
      have := (hasDerivAt_id r).mul_const (DW (0, Z) (0, 1))
      simpa [one_mul] using this
    have hsum : HasDerivAt g (DV (r, Z) (1, 0) + 1 * DW (0, Z) (0, 1)) r :=
      hVderiv.add hlinear
    have hzero : DV (r, Z) (1, 0) + 1 * DW (0, Z) (0, 1) = 0 := by
      have hdiv_rz := hdiv (r, Z)
      have hdz_eq : DW (r, Z) (0, 1) = DW (0, Z) (0, 1) :=
        endpoint_dz_axial_const_rec W DW hW hWr r Z
      rw [hdz_eq] at hdiv_rz
      linarith only [hdiv_rz]
    rw [hzero] at hsum
    exact hsum.differentiableAt
  have hg_fderiv : ∀ r : ℝ, fderiv ℝ g r = 0 := by
    intro r
    have hVderiv : HasDerivAt (fun r' : ℝ => V (r', Z)) (DV (r, Z) (1, 0)) r :=
      hasDerivAt_radial_of_hasFDerivAt (hV (r, Z))
    have hlinear : HasDerivAt (fun r' : ℝ => r' * DW (0, Z) (0, 1))
        (1 * DW (0, Z) (0, 1)) r := by
      have := (hasDerivAt_id r).mul_const (DW (0, Z) (0, 1))
      simpa [one_mul] using this
    have hsum : HasDerivAt g (DV (r, Z) (1, 0) + 1 * DW (0, Z) (0, 1)) r :=
      hVderiv.add hlinear
    have hzero : DV (r, Z) (1, 0) + 1 * DW (0, Z) (0, 1) = 0 := by
      have hdiv_rz := hdiv (r, Z)
      have hdz_eq : DW (r, Z) (0, 1) = DW (0, Z) (0, 1) :=
        endpoint_dz_axial_const_rec W DW hW hWr r Z
      rw [hdz_eq] at hdiv_rz
      linarith only [hdiv_rz]
    rw [hzero] at hsum
    have hfderiv : HasFDerivAt g (0 : ℝ →L[ℝ] ℝ) r := by
      simpa using hsum.hasFDerivAt
    exact hfderiv.fderiv
  have hconst := is_const_of_fderiv_eq_zero hg_diff hg_fderiv R 0
  dsimp [g] at hconst
  have hzero_mul : (0 : ℝ) * DW (0, Z) (0, 1) = 0 := by simp
  rw [hzero_mul, add_zero] at hconst
  linarith only [hconst]

theorem endpoint_dz_axial_eq_zero_rec (V W : ℝ × ℝ → ℝ) (DV DW : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)) (M : ℝ)
    (hV : ∀ p : ℝ × ℝ, HasFDerivAt V (DV p) p)
    (hW : ∀ p : ℝ × ℝ, HasFDerivAt W (DW p) p)
    (hbdd : ∀ p : ℝ × ℝ, |V p| ≤ M)
    (hdiv : ∀ p : ℝ × ℝ, DV p (1, 0) + DW p (0, 1) = 0)
    (hWr : ∀ p : ℝ × ℝ, DW p (1, 0) = 0)
    (Z : ℝ) :
    DW ((0 : ℝ), Z) (0, 1) = 0 := by
  set c := DW ((0 : ℝ), Z) (0, 1) with hc
  have hM_nonneg : 0 ≤ M := by
    have h0 := hbdd ((0 : ℝ), Z)
    have h_abs_nonneg : 0 ≤ |V ((0 : ℝ), Z)| := abs_nonneg _
    linarith only [h_abs_nonneg, h0]
  have h_bound : ∀ r : ℝ, 0 ≤ r → |r * c| ≤ 2 * M := by
    intro r hr
    have heq := endpoint_radial_eq_rec V W DV DW hV hW hdiv hWr r Z
    have h_abs_diff : |r * DW ((0 : ℝ), Z) (0, 1)| = |V (0, Z) - V (r, Z)| := by
      rw [heq]
      congr 1
      ring
    rw [h_abs_diff]
    have h_triangle : |V (0, Z) - V (r, Z)| ≤ |V (0, Z)| + |V (r, Z)| := abs_sub _ _
    have hbdd0 : |V ((0 : ℝ), Z)| ≤ M := hbdd ((0 : ℝ), Z)
    have hbddr : |V (r, Z)| ≤ M := hbdd (r, Z)
    linarith only [h_triangle, hbdd0, hbddr]
  have hc_zero : c = 0 := eq_zero_of_abs_mul_le_of_nonneg (M := 2 * M) h_bound
  dsimp [c] at hc_zero
  exact hc_zero

theorem endpoint_dr_radial_eq_zero_rec (V W : ℝ × ℝ → ℝ) (DV DW : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)) (M : ℝ)
    (hV : ∀ p : ℝ × ℝ, HasFDerivAt V (DV p) p)
    (hW : ∀ p : ℝ × ℝ, HasFDerivAt W (DW p) p)
    (hbdd : ∀ p : ℝ × ℝ, |V p| ≤ M)
    (hdiv : ∀ p : ℝ × ℝ, DV p (1, 0) + DW p (0, 1) = 0)
    (hWr : ∀ p : ℝ × ℝ, DW p (1, 0) = 0)
    (p : ℝ × ℝ) :
    DV p (1, 0) = 0 := by
  obtain ⟨R, Z⟩ := p
  have hdiv_p := hdiv (R, Z)
  have hdz_eq : DW (R, Z) (0, 1) = DW ((0 : ℝ), Z) (0, 1) :=
    endpoint_dz_axial_const_rec W DW hW hWr R Z
  rw [hdz_eq] at hdiv_p
  have hdz_zero : DW ((0 : ℝ), Z) (0, 1) = 0 :=
    endpoint_dz_axial_eq_zero_rec V W DV DW M hV hW hbdd hdiv hWr Z
  rw [hdz_zero, add_zero] at hdiv_p
  linarith only [hdiv_p]

theorem endpoint_vanishing_rec (V W : ℝ × ℝ → ℝ) (DV DW : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)) (M : ℝ)
    (hV : ∀ p : ℝ × ℝ, HasFDerivAt V (DV p) p)
    (hW : ∀ p : ℝ × ℝ, HasFDerivAt W (DW p) p)
    (hbdd : ∀ p : ℝ × ℝ, |V p| ≤ M)
    (hdiv : ∀ p : ℝ × ℝ, DV p (1, 0) + DW p (0, 1) = 0)
    (hWr : ∀ p : ℝ × ℝ, DW p (1, 0) = 0) :
    (∀ p : ℝ × ℝ, DV p (1, 0) = 0) ∧ (∀ p : ℝ × ℝ, DW p (0, 1) = 0) := by
  refine ⟨?_, ?_⟩
  · exact fun p => endpoint_dr_radial_eq_zero_rec V W DV DW M hV hW hbdd hdiv hWr p
  · intro p
    obtain ⟨R, Z⟩ := p
    have hconst := endpoint_dz_axial_const_rec W DW hW hWr R Z
    have hzero := endpoint_dz_axial_eq_zero_rec V W DV DW M hV hW hbdd hdiv hWr Z
    rw [hconst, hzero]

end CIV
