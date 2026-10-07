/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Analysis.ArzelaAscoliC1Plane
public import LeanPool.CIVAxisymmetric.Zoom.RecedingContradictionAssembly

/-!
# The receding-axis case of `prop:aniso:small` fails

Closing argument of *Step 3* of the zoom-in of Section `sec:aniso:zoom`
(`eq:aniso:zoom:receding:endpoint` and `eq:aniso:zoom:receding:quotient`).  In the recentred
variables `eq:aniso:zoom:receding:variables` the selected point is the origin of `ℝ × ℝ`, the
axis sits at `R = -A_n` with `A_n → ∞`, and the meridional fields live on the whole plane.

The bounds `eq:aniso:zoom:derivatives` make `V_n(·,-1)` and `W_n(·,-1)` bounded in `C²` on every
centred square with one constant, so along a subsequence they converge in `C¹` on those squares
(`CIV.exists_subseq_tendstoUniformlyOn_c1_plane`).  The limiting divergence identity is the
quotient-free `∂_R V⁰ + ∂_Z W⁰ = 0` of `eq:aniso:zoom:receding:div`, the term `V_n/(A_n+R)`
vanishing pointwise because `A_n → ∞` while `V_n` stays bounded; together with `∂_R W⁰ = 0`,
which comes from `Θ_n(·,-1) → 0`, this is exactly the input of
`CIV.endpoint_vanishing_rec`, the whole-plane bounded-affine argument.  The final step is
`CIV.false_of_receding_contradiction_data`, whose limit and convergence hypotheses are supplied
here by the extraction rather than assumed.

Everything here happens at the single time `τ = -1`: the compactness used is the spatial `C¹`
compactness of a fixed time slice, and no equicontinuity in `τ` is claimed or needed.  The two
inputs that carry information from the equation — the recentred divergence identity of
`eq:aniso:zoom:receding:div` and the vanishing of `∂_R W_n`, which comes from `Θ_n → 0` — enter
as hypotheses on the sequence itself.

The `C²` bounds are asked for all large `n` on each square, since the preimage of the unit
cylinder contains a given compact set only once the scale is small enough; the sequence is
therefore re-indexed past the threshold of the square of index `0` before the pointwise bound
`|V_n(0,0)| ≤ L` that `eq:aniso:zoom:receding:quotient` needs is read off.
-/

public section

open Set Filter Topology
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

/-! ### The endpoint data extracted from the `C²` bounds -/

/-- The endpoint data of `eq:aniso:zoom:receding:endpoint`, extracted rather than assumed: a
sequence of smooth meridional fields `(V_n, W_n)` on the plane which is `C²`-bounded by one
constant `L` on every centred square for all large `n`, satisfies the recentred divergence
identity of `eq:aniso:zoom:receding:div` for all large `n`, whose radial quotient
`V_n/(A_n+R)` tends to zero, and whose radial derivative `∂_R W_n` tends to zero, has a
subsequence along which the gradients converge uniformly on every centred square to gradients of
a pair `(V⁰, W⁰)` that is bounded by `L`, divergence free with no quotient term, and independent
of `R` in its axial component.

The seven conclusions are the seven hypotheses `hV`, `hW`, `hbdd`, `hdiv`, `hWr`, `hDVconv`,
`hDWconv` of `CIV.false_of_receding_contradiction_data`, with `M = L`. -/
theorem exists_subseq_receding_endpoint_data
    {L : ℝ} (hL : 0 ≤ L) (Anseq : ℕ → ℝ)
    (Vseq Wseq : ℕ → ℝ × ℝ → ℝ)
    (hVsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (Vseq n))
    (hWsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (Wseq n))
    (hVbdd : ∀ j : ℕ, ∀ᶠ n in atTop, ∀ y ∈ planeRectangle j,
      |Vseq n y| ≤ L ∧ ‖fderiv ℝ (Vseq n) y‖ ≤ L ∧ ‖fderiv ℝ (fderiv ℝ (Vseq n)) y‖ ≤ L)
    (hWbdd : ∀ j : ℕ, ∀ᶠ n in atTop, ∀ y ∈ planeRectangle j,
      |Wseq n y| ≤ L ∧ ‖fderiv ℝ (Wseq n) y‖ ≤ L ∧ ‖fderiv ℝ (fderiv ℝ (Wseq n)) y‖ ≤ L)
    (hdivn : ∀ p : ℝ × ℝ, ∀ᶠ n in atTop,
      fderiv ℝ (Vseq n) p (1, 0) + Vseq n p / (Anseq n + p.1)
        + fderiv ℝ (Wseq n) p (0, 1) = 0)
    (hquot : ∀ p : ℝ × ℝ, Tendsto (fun n => Vseq n p / (Anseq n + p.1)) atTop (nhds 0))
    (hdWn : ∀ p : ℝ × ℝ, Tendsto (fun n => fderiv ℝ (Wseq n) p (1, 0)) atTop (nhds 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ V W : ℝ × ℝ → ℝ,
      ∃ DV DW : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ),
        (∀ p : ℝ × ℝ, HasFDerivAt V (DV p) p) ∧
        (∀ p : ℝ × ℝ, HasFDerivAt W (DW p) p) ∧
        (∀ p : ℝ × ℝ, |V p| ≤ L) ∧
        (∀ p : ℝ × ℝ, DV p (1, 0) + DW p (0, 1) = 0) ∧
        (∀ p : ℝ × ℝ, DW p (1, 0) = 0) ∧
        (∀ j : ℕ, TendstoUniformlyOn (fun n => fderiv ℝ (Vseq (φ n))) DV atTop
          (planeRectangle j)) ∧
        (∀ j : ℕ, TendstoUniformlyOn (fun n => fderiv ℝ (Wseq (φ n))) DW atTop
          (planeRectangle j)) := by
  classical
  obtain ⟨φ, hφ, V, DV, hVconv0, hDVconv0, -, hVlimbdd, hVderiv⟩ :=
    exists_subseq_tendstoUniformlyOn_c1_plane Vseq L hL hVsmooth hVbdd
  have hWbdd' : ∀ j : ℕ, ∀ᶠ n in atTop, ∀ y ∈ planeRectangle j,
      |Wseq (φ n) y| ≤ L ∧ ‖fderiv ℝ (Wseq (φ n)) y‖ ≤ L ∧
        ‖fderiv ℝ (fderiv ℝ (Wseq (φ n))) y‖ ≤ L :=
    fun j => hφ.tendsto_atTop.eventually (hWbdd j)
  obtain ⟨ψ, hψ, W, DW, -, hDWconv, -, -, hWderiv⟩ :=
    exists_subseq_tendstoUniformlyOn_c1_plane (fun n => Wseq (φ n)) L hL
      (fun n => hWsmooth _) hWbdd'
  have hχ : StrictMono (fun n => φ (ψ n)) := hφ.comp hψ
  have hVconv : ∀ j, TendstoUniformlyOn (fun n => Vseq (φ (ψ n))) V atTop
      (planeRectangle j) := fun j => tendstoUniformlyOn_comp_strictMono (hVconv0 j) hψ
  have hDVconv : ∀ j, TendstoUniformlyOn (fun n => fderiv ℝ (Vseq (φ (ψ n)))) DV atTop
      (planeRectangle j) := fun j => tendstoUniformlyOn_comp_strictMono (hDVconv0 j) hψ
  -- The limiting divergence identity of `eq:aniso:zoom:receding:div`, with no quotient term.
  have hdiv : ∀ p : ℝ × ℝ, DV p (1, 0) + DW p (0, 1) = 0 := by
    intro p
    obtain ⟨j, hj⟩ := exists_mem_planeRectangle p
    have h1 : Tendsto (fun n => fderiv ℝ (Vseq (φ (ψ n))) p (1, 0)) atTop
        (nhds (DV p (1, 0))) :=
      ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ))).continuous.tendsto
        (DV p)).comp ((hDVconv j).tendsto_at hj)
    have h3 : Tendsto (fun n => fderiv ℝ (Wseq (φ (ψ n))) p (0, 1)) atTop
        (nhds (DW p (0, 1))) :=
      ((ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), (1 : ℝ))).continuous.tendsto
        (DW p)).comp ((hDWconv j).tendsto_at hj)
    have h2 : Tendsto (fun n => Vseq (φ (ψ n)) p / (Anseq (φ (ψ n)) + p.1)) atTop (nhds 0) :=
      (hquot p).comp hχ.tendsto_atTop
    have hev : ∀ᶠ n in atTop, fderiv ℝ (Vseq (φ (ψ n))) p (1, 0)
        + Vseq (φ (ψ n)) p / (Anseq (φ (ψ n)) + p.1)
        + fderiv ℝ (Wseq (φ (ψ n))) p (0, 1) = 0 :=
      hχ.tendsto_atTop.eventually (hdivn p)
    have hlim : DV p (1, 0) + 0 + DW p (0, 1) = 0 :=
      tendsto_nhds_unique (Filter.Tendsto.congr' hev ((h1.add h2).add h3)) tendsto_const_nhds
    linarith only [hlim]
  -- The axial component of the limit does not depend on the radius.
  have hWr : ∀ p : ℝ × ℝ, DW p (1, 0) = 0 := by
    intro p
    obtain ⟨j, hj⟩ := exists_mem_planeRectangle p
    have h1 : Tendsto (fun n => fderiv ℝ (Wseq (φ (ψ n))) p (1, 0)) atTop
        (nhds (DW p (1, 0))) :=
      ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : ℝ))).continuous.tendsto
        (DW p)).comp ((hDWconv j).tendsto_at hj)
    exact tendsto_nhds_unique h1 ((hdWn p).comp hχ.tendsto_atTop)
  exact ⟨fun n => φ (ψ n), hχ, V, W, DV, DW, hVderiv, hWderiv, hVlimbdd, hdiv, hWr,
    hDVconv, hDWconv⟩

/-! ### The contradiction -/

/-- *Step 3* of `prop:aniso:small` closes: a sequence of meridional fields `(V_n, W_n)` in the
recentred variables, with the endpoint data of `CIV.exists_subseq_receding_endpoint_data` and
receding offsets `A_n → ∞`, cannot satisfy the selection bound `eq:aniso:zoom:selected` at the
origin.  The extraction supplies exactly the convergence and limit hypotheses of
`CIV.false_of_receding_contradiction_data`, which then produces the contradiction. -/
theorem step_receding_contradiction
    {c₀ L : ℝ} (hc₀ : 0 < c₀) (hL : 0 ≤ L) {Anseq : ℕ → ℝ}
    (hAtop : Tendsto Anseq atTop atTop) (hApos : ∀ n, 0 < Anseq n)
    (Vseq Wseq : ℕ → ℝ × ℝ → ℝ)
    (hVsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (Vseq n))
    (hWsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (Wseq n))
    (hVbdd : ∀ j : ℕ, ∀ᶠ n in atTop, ∀ y ∈ planeRectangle j,
      |Vseq n y| ≤ L ∧ ‖fderiv ℝ (Vseq n) y‖ ≤ L ∧ ‖fderiv ℝ (fderiv ℝ (Vseq n)) y‖ ≤ L)
    (hWbdd : ∀ j : ℕ, ∀ᶠ n in atTop, ∀ y ∈ planeRectangle j,
      |Wseq n y| ≤ L ∧ ‖fderiv ℝ (Wseq n) y‖ ≤ L ∧ ‖fderiv ℝ (fderiv ℝ (Wseq n)) y‖ ≤ L)
    (hdivn : ∀ p : ℝ × ℝ, ∀ᶠ n in atTop,
      fderiv ℝ (Vseq n) p (1, 0) + Vseq n p / (Anseq n + p.1)
        + fderiv ℝ (Wseq n) p (0, 1) = 0)
    (hquot : ∀ p : ℝ × ℝ, Tendsto (fun n => Vseq n p / (Anseq n + p.1)) atTop (nhds 0))
    (hdWn : ∀ p : ℝ × ℝ, Tendsto (fun n => fderiv ℝ (Wseq n) p (1, 0)) atTop (nhds 0))
    (hlower : ∀ n, c₀ ≤ |fderiv ℝ (Vseq n) (0, 0) (1, 0)| + |Vseq n (0, 0)| / Anseq n
      + |fderiv ℝ (Wseq n) (0, 0) (0, 1)|) :
    False := by
  obtain ⟨φ, hφ, V, W, DV, DW, hV, hW, hbdd, hdiv, hWr, hDVconv, hDWconv⟩ :=
    exists_subseq_receding_endpoint_data hL Anseq Vseq Wseq hVsmooth hWsmooth hVbdd hWbdd
      hdivn hquot hdWn
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hVbdd 0)
  have hshift : StrictMono (fun n : ℕ => n + N) := fun a b hab => by simpa using hab
  have hχ : StrictMono (fun n : ℕ => φ (n + N)) := hφ.comp hshift
  have hge : ∀ n : ℕ, N ≤ φ (n + N) := fun n =>
    le_trans (Nat.le_add_left N n) hφ.le_apply
  refine false_of_receding_contradiction_data hc₀ V W DV DW hV hW hbdd hdiv hWr
    (fun n => fderiv ℝ (Vseq (φ (n + N)))) (fun n => fderiv ℝ (Wseq (φ (n + N))))
    (fun n => Vseq (φ (n + N))) (planeRectangle 0) (zero_mem_planeRectangle 0)
    (tendstoUniformlyOn_comp_strictMono (hDVconv 0) hshift)
    (tendstoUniformlyOn_comp_strictMono (hDWconv 0) hshift)
    (hAtop.comp hχ.tendsto_atTop) (fun n => hApos _) (fun n => ?_) (fun n => hlower _)
  exact (hN _ (hge n) ((0 : ℝ), (0 : ℝ)) (zero_mem_planeRectangle 0)).1

end CIV
