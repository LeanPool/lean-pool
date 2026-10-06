/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.EndpointFiniteAxis
public import LeanPool.CIVAxisymmetric.Zoom.FiniteSelectionIdentity

/-!
### Uniform convergence along a varying point -/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-- If `F n` converges uniformly to `f` on a set `S` and `x n ∈ S` for all `n`, then
`F n (x n) - f (x n) → 0`.  This is the elementary fact that pointwise convergence along a
sequence of points in the domain follows from uniform convergence on that domain. -/
theorem tendsto_of_tendstoUniformlyOn_of_mem_forall
    (S : Set (ℝ × ℝ)) (F : ℕ → ℝ × ℝ → ℝ) (f : ℝ × ℝ → ℝ)
    (hF : TendstoUniformlyOn F f atTop S) {x : ℕ → ℝ × ℝ} (hx : ∀ n, x n ∈ S) :
    Tendsto (fun n => F n (x n) - f (x n)) atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Metric.tendstoUniformlyOn_iff] at hF
  have hmem : ∀ᶠ n in atTop, ∀ y ∈ S, dist (f y) (F n y) < ε := hF ε hε
  filter_upwards [hmem] with n hn
  have hdist := hn (x n) (hx n)
  rw [Real.dist_eq] at hdist
  rw [Real.dist_eq, sub_zero, ← abs_sub_comm]
  exact hdist

/-!
### Vanishing of the absolute value along a varying point -/

/-- If `F n` converges uniformly to `0` on a set `S` and `x n ∈ S` for all `n`, then
`|F n (x n)| → 0`.  Follows directly from the previous lemma. -/
theorem abs_tendsto_zero_of_tendstoUniformlyOn_zero
    (S : Set (ℝ × ℝ)) (F : ℕ → ℝ × ℝ → ℝ)
    (hF : TendstoUniformlyOn F (fun _ => (0 : ℝ)) atTop S) {x : ℕ → ℝ × ℝ} (hx : ∀ n, x n ∈ S) :
    Tendsto (fun n => |F n (x n)|) atTop (nhds 0) := by
  have h := tendsto_of_tendstoUniformlyOn_of_mem_forall S F (fun _ => (0 : ℝ)) hF hx
  simpa [sub_zero, abs_zero] using h.abs

/-!
### Final contradiction of Step 2 -/

/-- The final contradiction of the finite-axis zoom. The endpoint theorem
`CIV.endpoint_tendstoUniformlyOn_triple` makes the radial derivative, the radial quotient
and the axial derivative converge uniformly to `0` on `[0, A] × {0}`, hence along the
selected sequence `(R n, 0)`, while `hlower` keeps their combination at least `c₀ > 0`.

`hlower` carries the factor `2` on the radial derivative, which is the form in which
`CIV.neg_t_mul_meridionalQuantity_selection_le` bounds the selected quantity of
`eq:aniso:zoom:selected`. On the axis the manuscript's `u_r / r` is `∂_r u_r`
(`CIV.radialQuotient_on_axis`), whereas the quotient `Vn n (R n, 0) / R n` written here is
`0` at `R n = 0`; the doubled radial derivative is what carries that summand across the
axis. All three terms tend to `0`, so the factor costs nothing here. -/
theorem false_of_finite_contradiction_data
    {A c₀ : ℝ} (hA : 0 < A) (hc₀ : 0 < c₀)
    (V W : ℝ × ℝ → ℝ) (DV DW : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)) (M : ℝ)
    (hV : ∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt V (DV p) p)
    (hW : ∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt W (DW p) p)
    (hbdd : ∀ p : ℝ × ℝ, 0 < p.1 → |V p| ≤ M)
    (hdiv : ∀ p : ℝ × ℝ, 0 < p.1 → DV p (1, 0) + V p / p.1 + DW p (0, 1) = 0)
    (hWr : ∀ p : ℝ × ℝ, 0 < p.1 → DW p (1, 0) = 0)
    (hDVcont : ContinuousOn (fun r : ℝ => DV (r, 0) (1, 0)) (Icc 0 A))
    (hDWcont : ContinuousOn (fun r : ℝ => DW (r, 0) (0, 1)) (Icc 0 A))
    (Vn : ℕ → ℝ × ℝ → ℝ) (DVn DWn : ℕ → ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ))
    (hDVconv : TendstoUniformlyOn DVn DV atTop (Icc (0 : ℝ) A ×ˢ ({0} : Set ℝ)))
    (hDWconv : TendstoUniformlyOn DWn DW atTop (Icc (0 : ℝ) A ×ˢ ({0} : Set ℝ)))
    (haxis : ∀ n, Vn n (0, 0) = 0)
    (hVncont : ∀ n, ContinuousOn (fun r : ℝ => Vn n (r, 0)) (Icc 0 A))
    (hVnderiv : ∀ n, ∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt (Vn n) (DVn n p) p)
    {R : ℕ → ℝ} (hRmem : ∀ n, R n ∈ Icc (0 : ℝ) A)
    (hlower : ∀ᶠ n in atTop, c₀ ≤ 2 * |DVn n (R n, 0) (1, 0)| + |Vn n (R n, 0) / (R n)|
      + |DWn n (R n, 0) (0, 1)|) :
    False := by
  set S : Set (ℝ × ℝ) := Icc (0 : ℝ) A ×ˢ ({0} : Set ℝ) with hS
  have htrip := CIV.endpoint_tendstoUniformlyOn_triple A 0 M hA V W DV DW Vn DVn DWn
    hV hW hbdd hdiv hWr hDVcont hDWcont hDVconv hDWconv haxis hVncont hVnderiv
  rcases htrip with ⟨hDVtend, hDWtend, hVtend⟩
  have hx_mem : ∀ n, (R n, 0) ∈ S := by
    intro n
    dsimp [S]
    exact ⟨hRmem n, rfl⟩
  have h1raw : Tendsto (fun n => |DVn n (R n, 0) (1, 0)|) atTop (nhds 0) :=
    abs_tendsto_zero_of_tendstoUniformlyOn_zero S (fun n p => DVn n p (1, 0)) hDVtend hx_mem
  have h1 : Tendsto (fun n => 2 * |DVn n (R n, 0) (1, 0)|) atTop (nhds 0) := by
    simpa [mul_zero] using h1raw.const_mul (2 : ℝ)
  have h2 : Tendsto (fun n => |Vn n (R n, 0) / (R n)|) atTop (nhds 0) := by
    have h2raw := abs_tendsto_zero_of_tendstoUniformlyOn_zero S (fun n p => Vn n p / p.1) hVtend
      hx_mem
    simpa using h2raw
  have h3 : Tendsto (fun n => |DWn n (R n, 0) (0, 1)|) atTop (nhds 0) :=
    abs_tendsto_zero_of_tendstoUniformlyOn_zero S (fun n p => DWn n p (0, 1)) hDWtend hx_mem
  have hsum : Tendsto (fun n => 2 * |DVn n (R n, 0) (1, 0)| + |Vn n (R n, 0) / (R n)|
      + |DWn n (R n, 0) (0, 1)|) atTop (nhds ((0 : ℝ) + 0 + 0)) :=
    (h1.add h2).add h3
  have hsum0 : Tendsto (fun n => 2 * |DVn n (R n, 0) (1, 0)| + |Vn n (R n, 0) / (R n)|
      + |DWn n (R n, 0) (0, 1)|) atTop (nhds 0) := by
    simpa [add_assoc] using hsum
  have hle : c₀ ≤ (0 : ℝ) :=
    ge_of_tendsto hsum0 hlower
  linarith only [hc₀, hle]

end CIV
