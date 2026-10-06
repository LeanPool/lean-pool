/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Analysis.ArzelaAscoliC1HalfPlane
public import LeanPool.CIVAxisymmetric.Zoom.FiniteContradictionAssembly

/-!
# The finite-axis case of `prop:aniso:small` fails

Closing argument of *Step 2* of the zoom-in of Section `sec:aniso:zoom`
(`eq:aniso:zoom:finite:endpoint` and the paragraph after it).  In the variables
`eq:aniso:zoom:finite:variables` the selected point `(x_n, t_n)` has coordinates
`(R, Z, τ) = (r_n/λ_n, 0, -1)`, and `(r_n/λ_n, 0)` lies in the compact set `[0, A] × {0}`.  By
`eq:aniso:zoom:fields` and the chain rule the selected quantity
`(-t_n)(|∂_r u_r| + |u_r/r| + |∂_z u_z|)(x_n, t_n)` equals
`(|∂_R V_n| + |V_n/R| + |∂_Z W_n|)(r_n/λ_n, 0, -1)`, both quotients extended continuously to the
axis.

The bounds `eq:aniso:zoom:derivatives` make `V_n(·,-1)` and `W_n(·,-1)` bounded in `C²` on every
compact subset of the closed half-plane with one constant, so along a subsequence they converge
in `C¹` on those compact sets.  The limits obey `∂_R V⁰ + V⁰/R + ∂_Z W⁰ = 0` and `∂_R W⁰ = 0`,
and the endpoint argument `CIV.endpoint_tendstoUniformlyOn_triple` turns this into the uniform
vanishing `eq:aniso:zoom:finite:endpoint` on `[0, A] × {0}`.  The selected quantity therefore
tends to zero along the subsequence, contradicting its lower bound `c₀ > 0` in
`eq:aniso:zoom:selected`; that last step is `CIV.false_of_finite_contradiction_data`, whose nine
limit and convergence hypotheses are supplied here by the extraction rather than assumed.

Everything here happens at the single time `τ = -1`: the compactness used is the spatial `C¹`
compactness `CIV.exists_subseq_tendstoUniformlyOn_c1_halfPlane` on a fixed time slice, and no
equicontinuity in `τ` is claimed or needed.  The two inputs that carry information from the
equation — the divergence identity of `eq:aniso:zoom:finite:identities` and the vanishing of
`∂_R W_n` off the axis, which comes from `Ω_n → 0` through the
potential-vorticity identity `CIV.zoomOmega_eq` — enter as hypotheses on the sequence itself.

The factor `2` in the lower bound is the one produced by
`CIV.lt_of_neg_t_mul_meridionalQuantity_selection_lt`, which absorbs the axis value of the
quotient `u_r/r` into the radial derivative; it costs nothing, since all three terms are shown to
vanish.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-! ### Evaluation of a convergent sequence of continuous linear maps -/

/-- Evaluation at a fixed vector is continuous, so a convergent sequence of continuous linear
maps converges at every vector. -/
theorem tendsto_clm_apply_of_tendsto {F : ℕ → (ℝ × ℝ) →L[ℝ] ℝ} {G : (ℝ × ℝ) →L[ℝ] ℝ}
    (h : Tendsto F atTop (nhds G)) (v : ℝ × ℝ) :
    Tendsto (fun n => F n v) atTop (nhds (G v)) :=
  ((ContinuousLinearMap.apply ℝ ℝ v).continuous.tendsto G).comp h

/-! ### The endpoint data extracted from the `C²` bounds -/

/-- The endpoint data of `eq:aniso:zoom:finite:endpoint`, extracted rather than assumed: a
sequence of smooth meridional fields `(V_n, W_n)` on the plane which is `C²`-bounded by one
constant `L` on every square `[0, j+1] × [-(j+1), j+1]` for all large `n`, satisfies the
divergence identity of `eq:aniso:zoom:finite:identities` off the axis for all large `n`, and
whose radial derivative `∂_R W_n` tends to zero off the axis, has a subsequence along which
`(V_n, W_n)` converges in `C¹` on every such square to a pair `(V⁰, W⁰)` that is bounded by `L`
on the open half-plane, divergence free there, and independent of `R` in its axial component.

The nine conclusions are exactly the nine hypotheses `hV`, `hW`, `hbdd`, `hdiv`, `hWr`,
`hDVcont`, `hDWcont`, `hDVconv`, `hDWconv` of `CIV.false_of_finite_contradiction_data`, in that
order, with `M = L`, `Vn n = V_{φ n}`, `DVn n = ∇V_{φ n}` and `DWn n = ∇W_{φ n}`. -/
theorem exists_subseq_finite_endpoint_data
    {A L : ℝ} (hL : 0 ≤ L)
    (Vseq Wseq : ℕ → ℝ × ℝ → ℝ)
    (hVsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (Vseq n))
    (hWsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (Wseq n))
    (hVbdd : ∀ j : ℕ, ∀ᶠ n in atTop, ∀ y ∈ halfPlaneRectangle j,
      |Vseq n y| ≤ L ∧ ‖fderiv ℝ (Vseq n) y‖ ≤ L ∧ ‖fderiv ℝ (fderiv ℝ (Vseq n)) y‖ ≤ L)
    (hWbdd : ∀ j : ℕ, ∀ᶠ n in atTop, ∀ y ∈ halfPlaneRectangle j,
      |Wseq n y| ≤ L ∧ ‖fderiv ℝ (Wseq n) y‖ ≤ L ∧ ‖fderiv ℝ (fderiv ℝ (Wseq n)) y‖ ≤ L)
    (hdivn : ∀ p : ℝ × ℝ, 0 < p.1 → ∀ᶠ n in atTop,
      fderiv ℝ (Vseq n) p (1, 0) + Vseq n p / p.1 + fderiv ℝ (Wseq n) p (0, 1) = 0)
    (hdWn : ∀ p : ℝ × ℝ, 0 < p.1 →
      Tendsto (fun n => fderiv ℝ (Wseq n) p (1, 0)) atTop (nhds 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ V W : ℝ × ℝ → ℝ,
      ∃ DV DW : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ),
        (∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt V (DV p) p) ∧
        (∀ p : ℝ × ℝ, 0 < p.1 → HasFDerivAt W (DW p) p) ∧
        (∀ p : ℝ × ℝ, 0 < p.1 → |V p| ≤ L) ∧
        (∀ p : ℝ × ℝ, 0 < p.1 → DV p (1, 0) + V p / p.1 + DW p (0, 1) = 0) ∧
        (∀ p : ℝ × ℝ, 0 < p.1 → DW p (1, 0) = 0) ∧
        ContinuousOn (fun r : ℝ => DV (r, 0) (1, 0)) (Icc 0 A) ∧
        ContinuousOn (fun r : ℝ => DW (r, 0) (0, 1)) (Icc 0 A) ∧
        TendstoUniformlyOn (fun n => fderiv ℝ (Vseq (φ n))) DV atTop
          (Icc (0 : ℝ) A ×ˢ ({0} : Set ℝ)) ∧
        TendstoUniformlyOn (fun n => fderiv ℝ (Wseq (φ n))) DW atTop
          (Icc (0 : ℝ) A ×ˢ ({0} : Set ℝ)) := by
  classical
  -- `C¹` extraction for the radial component on the closed half-plane.
  obtain ⟨φ, hφ, V, DV, hVconv0, hDVconv0, hDVcont0, hVlimbdd, hVderiv⟩ :=
    exists_subseq_tendstoUniformlyOn_c1_halfPlane Vseq L hL hVsmooth hVbdd
  -- and for the axial component along that subsequence.
  have hWbdd' : ∀ j : ℕ, ∀ᶠ n in atTop, ∀ y ∈ halfPlaneRectangle j,
      |Wseq (φ n) y| ≤ L ∧ ‖fderiv ℝ (Wseq (φ n)) y‖ ≤ L ∧
        ‖fderiv ℝ (fderiv ℝ (Wseq (φ n))) y‖ ≤ L :=
    fun j => hφ.tendsto_atTop.eventually (hWbdd j)
  obtain ⟨ψ, hψ, W, DW, -, hDWconv, hDWcont0, -, hWderiv⟩ :=
    exists_subseq_tendstoUniformlyOn_c1_halfPlane (fun n => Wseq (φ n)) L hL
      (fun n => hWsmooth _) hWbdd'
  have hχ : StrictMono (fun n => φ (ψ n)) := hφ.comp hψ
  have hVconv : ∀ j, TendstoUniformlyOn (fun n => Vseq (φ (ψ n))) V atTop
      (halfPlaneRectangle j) := fun j => tendstoUniformlyOn_comp_strictMono (hVconv0 j) hψ
  have hDVconv : ∀ j, TendstoUniformlyOn (fun n => fderiv ℝ (Vseq (φ (ψ n)))) DV atTop
      (halfPlaneRectangle j) := fun j => tendstoUniformlyOn_comp_strictMono (hDVconv0 j) hψ
  -- The limiting divergence identity, from `eq:aniso:zoom:finite:identities` at finite `n`.
  have hdiv : ∀ p : ℝ × ℝ, 0 < p.1 → DV p (1, 0) + V p / p.1 + DW p (0, 1) = 0 := by
    intro p hp
    obtain ⟨j, hj⟩ := exists_mem_halfPlaneRectangle hp.le
    have h1 := tendsto_clm_apply_of_tendsto ((hDVconv j).tendsto_at hj) (1, 0)
    have h2 := ((hVconv j).tendsto_at hj).div_const p.1
    have h3 := tendsto_clm_apply_of_tendsto ((hDWconv j).tendsto_at hj) (0, 1)
    have hev : ∀ᶠ n in atTop, fderiv ℝ (Vseq (φ (ψ n))) p (1, 0) + Vseq (φ (ψ n)) p / p.1
        + fderiv ℝ (Wseq (φ (ψ n))) p (0, 1) = 0 :=
      hχ.tendsto_atTop.eventually (hdivn p hp)
    exact tendsto_nhds_unique (Filter.Tendsto.congr' hev ((h1.add h2).add h3))
      tendsto_const_nhds
  -- The axial component of the limit does not depend on the radius.
  have hWr : ∀ p : ℝ × ℝ, 0 < p.1 → DW p (1, 0) = 0 := by
    intro p hp
    obtain ⟨j, hj⟩ := exists_mem_halfPlaneRectangle hp.le
    have h1 := tendsto_clm_apply_of_tendsto ((hDWconv j).tendsto_at hj) (1, 0)
    exact tendsto_nhds_unique h1 ((hdWn p hp).comp hχ.tendsto_atTop)
  -- The segment `[0, A] × {0}` sits in one square.
  obtain ⟨jA, hjA⟩ := exists_nat_ge A
  have hAle : A ≤ (jA : ℝ) + 1 := by linarith only [hjA]
  have hsub : Icc (0 : ℝ) A ×ˢ ({0} : Set ℝ) ⊆ halfPlaneRectangle jA :=
    segment_subset_halfPlaneRectangle hAle
  have hline : Continuous fun r : ℝ => (r, (0 : ℝ)) := continuous_id.prodMk continuous_const
  have hmaps : MapsTo (fun r : ℝ => (r, (0 : ℝ))) (Icc 0 A) (halfPlaneRectangle jA) :=
    fun r hr => hsub ⟨hr, rfl⟩
  exact ⟨fun n => φ (ψ n), hχ, V, W, DV, DW, hVderiv, hWderiv,
    (fun p hp => hVlimbdd p hp.le), hdiv, hWr,
    (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ))).continuous.comp_continuousOn
      ((hDVcont0 jA).comp hline.continuousOn hmaps),
    (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ))).continuous.comp_continuousOn
      ((hDWcont0 jA).comp hline.continuousOn hmaps),
    (hDVconv jA).mono hsub, (hDWconv jA).mono hsub⟩

/-! ### The endpoint vanishing on the axis segment -/

/-- `eq:aniso:zoom:finite:endpoint` on the segment `[0, A] × {0}`: along the subsequence of
`CIV.exists_subseq_finite_endpoint_data`, the radial derivative `∂_R V_n`, the axial derivative
`∂_Z W_n` and the quotient `V_n/R` all tend to zero uniformly there, the axis included. -/
theorem step_finite_endpoint
    {A L : ℝ} (hA : 0 < A) (hL : 0 ≤ L)
    (Vseq Wseq : ℕ → ℝ × ℝ → ℝ)
    (hVsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (Vseq n))
    (hWsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (Wseq n))
    (hVbdd : ∀ j : ℕ, ∀ᶠ n in atTop, ∀ y ∈ halfPlaneRectangle j,
      |Vseq n y| ≤ L ∧ ‖fderiv ℝ (Vseq n) y‖ ≤ L ∧ ‖fderiv ℝ (fderiv ℝ (Vseq n)) y‖ ≤ L)
    (hWbdd : ∀ j : ℕ, ∀ᶠ n in atTop, ∀ y ∈ halfPlaneRectangle j,
      |Wseq n y| ≤ L ∧ ‖fderiv ℝ (Wseq n) y‖ ≤ L ∧ ‖fderiv ℝ (fderiv ℝ (Wseq n)) y‖ ≤ L)
    (haxis : ∀ n, Vseq n (0, 0) = 0)
    (hdivn : ∀ p : ℝ × ℝ, 0 < p.1 → ∀ᶠ n in atTop,
      fderiv ℝ (Vseq n) p (1, 0) + Vseq n p / p.1 + fderiv ℝ (Wseq n) p (0, 1) = 0)
    (hdWn : ∀ p : ℝ × ℝ, 0 < p.1 →
      Tendsto (fun n => fderiv ℝ (Wseq n) p (1, 0)) atTop (nhds 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformlyOn (fun n p => fderiv ℝ (Vseq (φ n)) p (1, 0)) (fun _ => (0 : ℝ)) atTop
        (Icc (0 : ℝ) A ×ˢ ({0} : Set ℝ)) ∧
      TendstoUniformlyOn (fun n p => fderiv ℝ (Wseq (φ n)) p (0, 1)) (fun _ => (0 : ℝ)) atTop
        (Icc (0 : ℝ) A ×ˢ ({0} : Set ℝ)) ∧
      TendstoUniformlyOn (fun n p => Vseq (φ n) p / p.1) (fun _ => (0 : ℝ)) atTop
        (Icc (0 : ℝ) A ×ˢ ({0} : Set ℝ)) := by
  obtain ⟨φ, hφ, V, W, DV, DW, hV, hW, hbdd, hdiv, hWr, hDVcont, hDWcont, hDVconv, hDWconv⟩ :=
    exists_subseq_finite_endpoint_data (A := A) hL Vseq Wseq hVsmooth hWsmooth hVbdd hWbdd
      hdivn hdWn
  have hline : Continuous fun r : ℝ => (r, (0 : ℝ)) := continuous_id.prodMk continuous_const
  obtain ⟨hDVtend, hDWtend, hVtend⟩ := endpoint_tendstoUniformlyOn_triple A 0 L hA V W DV DW
    (fun n => Vseq (φ n)) (fun n => fderiv ℝ (Vseq (φ n))) (fun n => fderiv ℝ (Wseq (φ n)))
    hV hW hbdd hdiv hWr hDVcont hDWcont hDVconv hDWconv (fun n => haxis _)
    (fun n => ((hVsmooth (φ n)).continuous.comp hline).continuousOn)
    (fun n p _ => ((contDiff_infty_iff_fderiv.mp (hVsmooth (φ n))).1 p).hasFDerivAt)
  exact ⟨φ, hφ, hDVtend, hDWtend, hVtend⟩

/-! ### The contradiction -/

/-- *Step 2* of `prop:aniso:small` closes: a sequence of meridional fields `(V_n, W_n)` with the
endpoint data of `CIV.exists_subseq_finite_endpoint_data` cannot satisfy the selection bound
`eq:aniso:zoom:selected` at radii `R_n ∈ [0, A]`.  The extraction supplies exactly the nine
convergence and limit hypotheses of `CIV.false_of_finite_contradiction_data`, which then
produces the contradiction. -/
theorem step_finite_contradiction
    {A c₀ L : ℝ} (hA : 0 < A) (hc₀ : 0 < c₀) (hL : 0 ≤ L)
    (Vseq Wseq : ℕ → ℝ × ℝ → ℝ)
    (hVsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (Vseq n))
    (hWsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (Wseq n))
    (hVbdd : ∀ j : ℕ, ∀ᶠ n in atTop, ∀ y ∈ halfPlaneRectangle j,
      |Vseq n y| ≤ L ∧ ‖fderiv ℝ (Vseq n) y‖ ≤ L ∧ ‖fderiv ℝ (fderiv ℝ (Vseq n)) y‖ ≤ L)
    (hWbdd : ∀ j : ℕ, ∀ᶠ n in atTop, ∀ y ∈ halfPlaneRectangle j,
      |Wseq n y| ≤ L ∧ ‖fderiv ℝ (Wseq n) y‖ ≤ L ∧ ‖fderiv ℝ (fderiv ℝ (Wseq n)) y‖ ≤ L)
    (haxis : ∀ n, Vseq n (0, 0) = 0)
    (hdivn : ∀ p : ℝ × ℝ, 0 < p.1 → ∀ᶠ n in atTop,
      fderiv ℝ (Vseq n) p (1, 0) + Vseq n p / p.1 + fderiv ℝ (Wseq n) p (0, 1) = 0)
    (hdWn : ∀ p : ℝ × ℝ, 0 < p.1 →
      Tendsto (fun n => fderiv ℝ (Wseq n) p (1, 0)) atTop (nhds 0))
    {Rsel : ℕ → ℝ} (hRmem : ∀ n, Rsel n ∈ Icc (0 : ℝ) A)
    (hlower : ∀ᶠ n in atTop, c₀ ≤ 2 * |fderiv ℝ (Vseq n) (Rsel n, 0) (1, 0)|
      + |Vseq n (Rsel n, 0) / Rsel n| + |fderiv ℝ (Wseq n) (Rsel n, 0) (0, 1)|) :
    False := by
  obtain ⟨φ, hφ, V, W, DV, DW, hV, hW, hbdd, hdiv, hWr, hDVcont, hDWcont, hDVconv, hDWconv⟩ :=
    exists_subseq_finite_endpoint_data (A := A) hL Vseq Wseq hVsmooth hWsmooth hVbdd hWbdd
      hdivn hdWn
  have hline : Continuous fun r : ℝ => (r, (0 : ℝ)) := continuous_id.prodMk continuous_const
  exact false_of_finite_contradiction_data hA hc₀ V W DV DW L hV hW hbdd hdiv hWr hDVcont
    hDWcont (fun n => Vseq (φ n)) (fun n => fderiv ℝ (Vseq (φ n)))
    (fun n => fderiv ℝ (Wseq (φ n))) hDVconv hDWconv (fun n => haxis _)
    (fun n => ((hVsmooth (φ n)).continuous.comp hline).continuousOn)
    (fun n p _ => ((contDiff_infty_iff_fderiv.mp (hVsmooth (φ n))).1 p).hasFDerivAt)
    (fun n => hRmem _) (hφ.tendsto_atTop.eventually hlower)

/-! ### The form produced by the selection bound -/

/-- The same contradiction, with the selected quantity written through the repository's `dr`,
`dz` of the space-time fields at the selected time `τ = -1`: this is the form in which
`CIV.lt_of_neg_t_mul_meridionalQuantity_selection_lt` delivers the lower bound
`eq:aniso:zoom:selected`, with `Vfield n = zoomV λ_n h z_n u` and `Wfield n = zoomW λ_n h z_n u`
and their `τ = -1` slices as `Vseq`, `Wseq`. -/
theorem step_finite_contradiction_of_dr_dz
    {A c₀ L : ℝ} (hA : 0 < A) (hc₀ : 0 < c₀) (hL : 0 ≤ L)
    (Vseq Wseq : ℕ → ℝ × ℝ → ℝ) (Vfield Wfield : ℕ → (ℝ × ℝ) × ℝ → ℝ)
    (hVslice : ∀ n, ∀ q : ℝ × ℝ, Vfield n (q, -1) = Vseq n q)
    (hWslice : ∀ n, ∀ q : ℝ × ℝ, Wfield n (q, -1) = Wseq n q)
    (hVsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (Vseq n))
    (hWsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (Wseq n))
    (hVbdd : ∀ j : ℕ, ∀ᶠ n in atTop, ∀ y ∈ halfPlaneRectangle j,
      |Vseq n y| ≤ L ∧ ‖fderiv ℝ (Vseq n) y‖ ≤ L ∧ ‖fderiv ℝ (fderiv ℝ (Vseq n)) y‖ ≤ L)
    (hWbdd : ∀ j : ℕ, ∀ᶠ n in atTop, ∀ y ∈ halfPlaneRectangle j,
      |Wseq n y| ≤ L ∧ ‖fderiv ℝ (Wseq n) y‖ ≤ L ∧ ‖fderiv ℝ (fderiv ℝ (Wseq n)) y‖ ≤ L)
    (haxis : ∀ n, Vseq n (0, 0) = 0)
    (hdivn : ∀ p : ℝ × ℝ, 0 < p.1 → ∀ᶠ n in atTop,
      fderiv ℝ (Vseq n) p (1, 0) + Vseq n p / p.1 + fderiv ℝ (Wseq n) p (0, 1) = 0)
    (hdWn : ∀ p : ℝ × ℝ, 0 < p.1 →
      Tendsto (fun n => fderiv ℝ (Wseq n) p (1, 0)) atTop (nhds 0))
    {Rsel : ℕ → ℝ} (hRmem : ∀ n, Rsel n ∈ Icc (0 : ℝ) A)
    (hlower : ∀ n, c₀ ≤ 2 * |dr (Vfield n) ((Rsel n, 0), (-1 : ℝ))|
      + |Vfield n ((Rsel n, 0), (-1 : ℝ)) / Rsel n|
      + |dz (Wfield n) ((Rsel n, 0), (-1 : ℝ))|) :
    False := by
  have hVfun : ∀ n, (fun q : ℝ × ℝ => Vfield n (q, (-1 : ℝ))) = Vseq n :=
    fun n => funext (hVslice n)
  have hWfun : ∀ n, (fun q : ℝ × ℝ => Wfield n (q, (-1 : ℝ))) = Wseq n :=
    fun n => funext (hWslice n)
  refine step_finite_contradiction hA hc₀ hL Vseq Wseq hVsmooth hWsmooth hVbdd hWbdd haxis
    hdivn hdWn hRmem (Filter.Eventually.of_forall fun n => ?_)
  have hVd : HasFDerivAt (fun q : ℝ × ℝ => Vfield n (q, (-1 : ℝ)))
      (fderiv ℝ (Vseq n) (Rsel n, 0)) (Rsel n, 0) := by
    rw [hVfun n]
    exact ((contDiff_infty_iff_fderiv.mp (hVsmooth n)).1 _).hasFDerivAt
  have hWd : HasFDerivAt (fun q : ℝ × ℝ => Wfield n (q, (-1 : ℝ)))
      (fderiv ℝ (Wseq n) (Rsel n, 0)) (Rsel n, 0) := by
    rw [hWfun n]
    exact ((contDiff_infty_iff_fderiv.mp (hWsmooth n)).1 _).hasFDerivAt
  have hdrn : dr (Vfield n) ((Rsel n, 0), (-1 : ℝ)) = fderiv ℝ (Vseq n) (Rsel n, 0) (1, 0) :=
    dr_eq_of_hasFDerivAt (Vfield n) (-1) hVd
  have hdzn : dz (Wfield n) ((Rsel n, 0), (-1 : ℝ)) = fderiv ℝ (Wseq n) (Rsel n, 0) (0, 1) :=
    dz_eq_of_hasFDerivAt (Wfield n) (-1) hWd
  have hval : Vfield n ((Rsel n, 0), (-1 : ℝ)) = Vseq n (Rsel n, 0) := hVslice n _
  have h := hlower n
  rw [hdrn, hdzn, hval] at h
  exact h

end CIV
