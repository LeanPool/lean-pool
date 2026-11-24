/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MaximalPsh
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PshSupremumRegularization
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.UscRegularizationContinuous
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PshClosedDiscMaximum
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HarmonicDiscPsh
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PlurisubharmonicPullback

/-!
# The Perron–Bremermann envelope on the unit polydisk

Let `P = {z ∈ ℂⁿ : ∀ i, ‖z i‖ < 1}` be the open unit polydisk and let `v` be a
continuous function on `PBar`.  The *Perron–Bremermann envelope* of `v` is

`u(z) = sup {w(z) : w` plurisubharmonic on `P`,
`limsup_{z → ζ} w(z) ≤ v(ζ)` for every `ζ ∈ ∂P}`.

This file sets up the envelope and proves its basic properties, following
Bedford–Taylor, *The Dirichlet problem for a complex Monge–Ampère equation*
(Invent. Math. 37 (1976), 1–44) and Z. Błocki, *The complex Monge–Ampère
operator in pluripotential theory*, lecture notes, §1.4 and §2.3:

* `self_le_perronEnvelope`: `v ≤ u` on `P` when `v` is itself plurisubharmonic;
* `perronEnvelope_le_of_forall_le`: `u` is bounded above by any bound for `v`
  on `PBar` — the upper barrier is built from a harmonic function of one
  coordinate, so that the one-variable maximum principle applies on every
  coordinate slice;
* `eventually_perronEnvelope_le`: `limsup_{z → ζ} u(z) ≤ v(ζ)` on `∂P`;
* `isPerronCompetitor_perronEnvelope`: `u` is itself a competitor, in
  particular plurisubharmonic on `P` (its upper-semicontinuous regularization
  is a competitor and lies below `u`);
* `isMaximalPshOn_perronEnvelope`: `u` is maximal on `P`, by gluing with
  `max (w, u)`.

The competitor class uses real-valued functions bounded on `P` and the boundary
condition in the `∀ ε > 0, ∀ᶠ z in 𝓝[P] ζ` form, which avoids `limsup` algebra
in `EReal`.
-/

@[expose] public section

noncomputable section

open Set Filter Metric TopologicalSpace InnerProductSpace
open scoped Topology ComplexConjugate

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere

variable {n : ℕ}

/-! ### The open unit polydisk and its boundary -/

/-- The open unit polydisk in `ℂⁿ`. -/
def unitPolydisk (n : ℕ) : Set (ComplexModel n) := {z | ∀ i, ‖z i‖ < 1}

/-- The closed unit polydisk in `ℂⁿ`. -/
def closedUnitPolydisk (n : ℕ) : Set (ComplexModel n) := {z | ∀ i, ‖z i‖ ≤ 1}

theorem mem_unitPolydisk_iff {z : ComplexModel n} :
    z ∈ unitPolydisk n ↔ ∀ i, ‖z i‖ < 1 := Iff.rfl

theorem mem_closedUnitPolydisk_iff {z : ComplexModel n} :
    z ∈ closedUnitPolydisk n ↔ ∀ i, ‖z i‖ ≤ 1 := Iff.rfl

theorem isOpen_unitPolydisk : IsOpen (unitPolydisk n) := by
  have : unitPolydisk n = ⋂ i : Fin n, {z : ComplexModel n | ‖z i‖ < 1} := by
    ext z; simp [unitPolydisk]
  rw [this]
  refine isOpen_iInter_of_finite fun i => ?_
  exact isOpen_lt (by fun_prop) continuous_const

theorem isClosed_closedUnitPolydisk : IsClosed (closedUnitPolydisk n) := by
  have : closedUnitPolydisk n = ⋂ i : Fin n, {z : ComplexModel n | ‖z i‖ ≤ 1} := by
    ext z; simp [closedUnitPolydisk]
  rw [this]
  refine isClosed_iInter fun i => ?_
  exact isClosed_le (by fun_prop) continuous_const

theorem unitPolydisk_subset_closedUnitPolydisk :
    unitPolydisk n ⊆ closedUnitPolydisk n := fun _ hz i => (hz i).le

theorem isBounded_closedUnitPolydisk :
    Bornology.IsBounded (closedUnitPolydisk n) := by
  refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨Real.sqrt n, fun z hz => ?_⟩
  rw [mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i : Fin n, ‖z i‖ ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := hz i
        nlinarith [norm_nonneg (z i)]
    _ = n := by simp

theorem isCompact_closedUnitPolydisk : IsCompact (closedUnitPolydisk n) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_closedUnitPolydisk
    isBounded_closedUnitPolydisk

theorem exists_norm_eq_one_of_mem_boundary {ζ : ComplexModel n}
    (hζ : ζ ∈ closedUnitPolydisk n \ unitPolydisk n) : ∃ j, ‖ζ j‖ = 1 := by
  obtain ⟨hmem, hnot⟩ := hζ
  by_contra hcon
  push Not at hcon
  exact hnot fun i => lt_of_le_of_ne (hmem i) (hcon i)

/-! ### Coordinate slices -/

/-- The complex line through `z` in the direction of the `j`-th coordinate,
parametrized so that the parameter is the `j`-th coordinate itself. -/
def coordinateSlice (z : ComplexModel n) (j : Fin n) (μ : ℂ) : ComplexModel n :=
  z + (μ - z j) • EuclideanSpace.single j (1 : ℂ)

theorem coordinateSlice_apply (z : ComplexModel n) (j : Fin n) (μ : ℂ) (i : Fin n) :
    coordinateSlice z j μ i = if i = j then μ else z i := by
  by_cases h : i = j <;> simp [coordinateSlice, h]

theorem coordinateSlice_self (z : ComplexModel n) (j : Fin n) :
    coordinateSlice z j (z j) = z := by
  ext i
  rw [coordinateSlice_apply]
  by_cases h : i = j <;> simp [h]

theorem continuous_coordinateSlice (z : ComplexModel n) (j : Fin n) :
    Continuous (coordinateSlice z j) := by
  unfold coordinateSlice
  fun_prop

theorem coordinateSlice_mem_closedUnitPolydisk {z : ComplexModel n} {j : Fin n}
    {μ : ℂ} (hz : z ∈ closedUnitPolydisk n) (hμ : ‖μ‖ ≤ 1) :
    coordinateSlice z j μ ∈ closedUnitPolydisk n := by
  intro i
  rw [coordinateSlice_apply]
  by_cases h : i = j <;> simp only [h, ite_eq_left, reduceIte]
  · exact hμ
  · exact hz i

theorem coordinateSlice_mem_unitPolydisk {z : ComplexModel n} {j : Fin n}
    {μ : ℂ} (hz : z ∈ unitPolydisk n) (hμ : ‖μ‖ < 1) :
    coordinateSlice z j μ ∈ unitPolydisk n := by
  intro i
  rw [coordinateSlice_apply]
  by_cases h : i = j <;> simp only [h, ite_eq_left, reduceIte]
  · exact hμ
  · exact hz i

theorem coordinateSlice_mem_boundary {z : ComplexModel n} {j : Fin n} {μ : ℂ}
    (hz : z ∈ unitPolydisk n) (hμ : ‖μ‖ = 1) :
    coordinateSlice z j μ ∈ closedUnitPolydisk n \ unitPolydisk n := by
  refine ⟨coordinateSlice_mem_closedUnitPolydisk
    (unitPolydisk_subset_closedUnitPolydisk hz) hμ.le, fun hmem => ?_⟩
  have := hmem j
  rw [coordinateSlice_apply, ite_eq_left rfl, hμ] at this
  exact lt_irrefl 1 this

theorem norm_coordinateSlice_sub_le (z ζ : ComplexModel n) (j : Fin n) (μ : ℂ) :
    ‖coordinateSlice z j μ - ζ‖ ≤ 2 * ‖z - ζ‖ + ‖μ - ζ j‖ := by
  have hsplit : coordinateSlice z j μ - ζ =
      (z - ζ) + (μ - z j) • EuclideanSpace.single j (1 : ℂ) := by
    unfold coordinateSlice; abel
  have hcoord : ‖(μ - z j) • EuclideanSpace.single j (1 : ℂ)‖ = ‖μ - z j‖ := by
    simp [norm_smul]
  have hzj : ‖z j - ζ j‖ ≤ ‖z - ζ‖ := by
    have := PiLp.norm_apply_le (z - ζ) j
    simpa using this
  have : ‖μ - z j‖ ≤ ‖μ - ζ j‖ + ‖z - ζ‖ := by
    calc ‖μ - z j‖ = ‖(μ - ζ j) + (ζ j - z j)‖ := by ring_nf
      _ ≤ ‖μ - ζ j‖ + ‖ζ j - z j‖ := norm_add_le _ _
      _ ≤ ‖μ - ζ j‖ + ‖z - ζ‖ := by rw [norm_sub_rev (ζ j)]; linarith
  calc ‖coordinateSlice z j μ - ζ‖ ≤ ‖z - ζ‖ +
        ‖(μ - z j) • EuclideanSpace.single j (1 : ℂ)‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ = ‖z - ζ‖ + ‖μ - z j‖ := by rw [hcoord]
    _ ≤ 2 * ‖z - ζ‖ + ‖μ - ζ j‖ := by linarith

/-- Plurisubharmonicity restricts to coordinate slices. -/
theorem plurisubharmonicOn_comp_coordinateSlice {w : ComplexModel n → EReal}
    {z : ComplexModel n} {j : Fin n} (hw : PlurisubharmonicOn w (unitPolydisk n))
    (hz : z ∈ unitPolydisk n) :
    PlurisubharmonicOn (fun μ : ℂ => w (coordinateSlice z j μ)) (ball (0 : ℂ) 1) := by
  set L : ℂ →L[ℂ] ComplexModel n :=
    ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (EuclideanSpace.single j (1 : ℂ)) with hLdef
  set b : ComplexModel n := z - z j • EuclideanSpace.single j (1 : ℂ) with hbdef
  have hpt : ∀ μ : ℂ, b + L μ = coordinateSlice z j μ := by
    intro μ
    rw [hLdef, hbdef]
    unfold coordinateSlice
    simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self,
      sub_smul]
    abel
  have hL := hw.comp_affine L b
  have hsub : ball (0 : ℂ) 1 ⊆ (fun y => b + L y) ⁻¹' unitPolydisk n := by
    intro μ hμ
    have hμ' : ‖μ‖ < 1 := by simpa using mem_ball_zero_iff.mp hμ
    have hmem := coordinateSlice_mem_unitPolydisk (j := j) hz hμ'
    simpa [hpt μ] using hmem
  have := hL.mono hsub
  simpa only [hpt] using this

/-! ### A maximum principle on the unit disc with boundary `limsup` data -/

/-- If a plurisubharmonic function on the open unit disc is eventually bounded
by `C + ε` near every boundary point, then it is bounded by `C` on the disc. -/
theorem le_of_eventually_le_on_unitSphere {u : ℂ → EReal}
    (hu : PlurisubharmonicOn u (ball (0 : ℂ) 1)) {C : ℝ}
    (hbd : ∀ ξ ∈ sphere (0 : ℂ) 1, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ μ in 𝓝[ball (0 : ℂ) 1] ξ, u μ ≤ ((C + ε : ℝ) : EReal)) :
    ∀ μ ∈ ball (0 : ℂ) 1, u μ ≤ (C : EReal) := by
  intro μ hμ
  have key : ∀ ε : ℝ, 0 < ε → u μ ≤ ((C + ε : ℝ) : EReal) := by
    intro ε hε
    set S : Set ℂ := {x | x ∈ ball (0 : ℂ) 1 → u x ≤ ((C + ε : ℝ) : EReal)} with hS
    have hsphere : sphere (0 : ℂ) 1 ⊆ interior S := by
      intro ξ hξ
      rw [mem_interior_iff_mem_nhds]
      have := hbd ξ hξ ε hε
      rw [eventually_nhdsWithin_iff] at this
      exact this
    obtain ⟨δ, hδ, hδsub⟩ := (isCompact_sphere (0 : ℂ) 1).exists_thickening_subset_open
      isOpen_interior hsphere
    set R : ℝ := max (1 - δ / 2) ((‖μ‖ + 1) / 2) with hR
    have hμnorm : ‖μ‖ < 1 := by simpa [Complex.norm_def] using mem_ball_zero_iff.mp hμ
    have hRlt : R < 1 := by
      refine max_lt ?_ ?_ <;> linarith
    have hμR : ‖μ‖ ≤ R := le_trans (by linarith) (le_max_right _ _)
    have hRpos : 0 < R := lt_of_lt_of_le (by positivity) (le_max_right _ _)
    have hball : closedBall (0 : ℂ) R ⊆ ball (0 : ℂ) 1 := by
      intro x hx
      rw [mem_closedBall, dist_zero_right] at hx
      exact mem_ball_zero_iff.mpr (lt_of_le_of_lt hx hRlt)
    have hspR : ∀ x ∈ sphere (0 : ℂ) R, u x ≤ ((C + ε : ℝ) : EReal) := by
      intro x hx
      rw [mem_sphere, dist_zero_right] at hx
      have hxne : x ≠ 0 := by
        intro h; rw [h, norm_zero] at hx; exact hRpos.ne hx
      set y : ℂ := ((R⁻¹ : ℝ) : ℂ) * x with hy
      have hynorm : ‖y‖ = 1 := by
        rw [hy, norm_mul, hx]
        simp [abs_of_pos hRpos, inv_mul_cancel₀ hRpos.ne']
      have hdist : dist x y < δ := by
        have hxy : x - y = ((1 - R⁻¹ : ℝ) : ℂ) * x := by
          rw [hy]; push_cast; ring
        have habs : |1 - R⁻¹| * R = 1 - R := by
          have hmul : |1 - R⁻¹| * R = |(1 - R⁻¹) * R| := by
            rw [abs_mul, abs_of_pos hRpos]
          have hprod : (1 - R⁻¹) * R = R - 1 := by
            field_simp
          rw [hmul, hprod, abs_of_nonpos (by linarith)]
          ring
        have hRmax : 1 - δ / 2 ≤ R := le_max_left _ _
        rw [dist_eq_norm, hxy, norm_mul, Complex.norm_real, Real.norm_eq_abs, hx,
          habs]
        linarith
      have hx_mem : x ∈ interior S :=
        hδsub (Metric.mem_thickening_iff.mpr ⟨y, by simpa using hynorm, hdist⟩)
      exact interior_subset hx_mem (hball (mem_closedBall.mpr (by
        rw [dist_zero_right, hx])))
    have := hu.le_const_on_closedBall_of_le_on_sphere hRpos hball hspR μ
      (mem_closedBall.mpr (by rw [dist_zero_right]; exact hμR))
    exact this
  refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
  induction a using EReal.rec with
  | bot => exact absurd ha (by simp)
  | top => exact le_top
  | coe x =>
      have hx : C < x := EReal.coe_lt_coe_iff.mp ha
      have := key (x - C) (by linarith)
      simpa using this

/-- Real parts of complex affine functions are harmonic; these are the only
barriers used below. -/
theorem harmonicOnNhd_affine_re (a b : ℂ) :
    HarmonicOnNhd (fun μ : ℂ => (a + b * μ).re) univ := by
  intro μ _
  have hA : AnalyticAt ℂ (fun μ : ℂ => a + b * μ) μ := by fun_prop
  exact hA.harmonicAt_re

/-! ### Competitors for the Perron–Bremermann envelope -/

/-- `w` is a competitor for the boundary data `v` on the unit polydisk: it is
plurisubharmonic on `P` and its boundary `limsup` is at most `v`. -/
def IsPerronCompetitor (v w : ComplexModel n → ℝ) : Prop :=
  PlurisubharmonicOn (fun z => (w z : EReal)) (unitPolydisk n) ∧
    ∀ ζ ∈ closedUnitPolydisk n \ unitPolydisk n, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in 𝓝[unitPolydisk n] ζ, w z ≤ v ζ + ε

/-- The one-variable maximum principle on a coordinate slice: a competitor is
dominated by every harmonic majorant of the boundary data along that slice. -/
theorem IsPerronCompetitor.le_harmonic {v w : ComplexModel n → ℝ}
    (hw : IsPerronCompetitor v w) {z : ComplexModel n} (hz : z ∈ unitPolydisk n)
    (j : Fin n) {H : ℂ → ℝ} (hH : HarmonicOnNhd H univ)
    (hvH : ∀ μ : ℂ, ‖μ‖ = 1 → v (coordinateSlice z j μ) ≤ H μ) :
    w z ≤ H (z j) := by
  have hslice := plurisubharmonicOn_comp_coordinateSlice (j := j) hw.1 hz
  have hHball : HarmonicOnNhd H (ball (0 : ℂ) 1) := fun μ _ => hH μ (mem_univ μ)
  have hsub : PlurisubharmonicOn
      (fun μ : ℂ => (w (coordinateSlice z j μ) : EReal) - (H μ : EReal))
      (ball (0 : ℂ) 1) := hslice.sub_harmonic hHball
  have hHcont : Continuous H := by
    rw [continuous_iff_continuousAt]
    intro μ
    exact ((hH μ (mem_univ μ)).1).continuousAt
  have hbd : ∀ ξ ∈ sphere (0 : ℂ) 1, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ μ in 𝓝[ball (0 : ℂ) 1] ξ,
        (w (coordinateSlice z j μ) : EReal) - (H μ : EReal) ≤ ((0 + ε : ℝ) : EReal) := by
    intro ξ hξ ε hε
    have hξnorm : ‖ξ‖ = 1 := by simpa using mem_sphere_zero_iff_norm.mp hξ
    have hbdry := coordinateSlice_mem_boundary (j := j) hz hξnorm
    have hev := hw.2 _ hbdry (ε / 2) (by linarith)
    have hmaps : MapsTo (coordinateSlice z j) (ball (0 : ℂ) 1) (unitPolydisk n) := by
      intro μ hμ
      exact coordinateSlice_mem_unitPolydisk hz (by simpa using mem_ball_zero_iff.mp hμ)
    have htend : Tendsto (coordinateSlice z j) (𝓝[ball (0 : ℂ) 1] ξ)
        (𝓝[unitPolydisk n] (coordinateSlice z j ξ)) :=
      ((continuous_coordinateSlice z j).continuousWithinAt).tendsto_nhdsWithin hmaps
    have hev' := htend.eventually hev
    have hHev : ∀ᶠ μ in 𝓝[ball (0 : ℂ) 1] ξ, H ξ - ε / 2 < H μ := by
      refine nhdsWithin_le_nhds ?_
      have hlt : H ξ - ε / 2 < H ξ := by linarith
      exact (hHcont.continuousAt (x := ξ)).eventually (eventually_gt_nhds hlt)
    filter_upwards [hev', hHev] with μ hμ hHμ
    have hvle : v (coordinateSlice z j ξ) ≤ H ξ := hvH ξ hξnorm
    have : w (coordinateSlice z j μ) - H μ ≤ 0 + ε := by
      have := hμ
      linarith
    calc (w (coordinateSlice z j μ) : EReal) - (H μ : EReal)
        = ((w (coordinateSlice z j μ) - H μ : ℝ) : EReal) := by rw [EReal.coe_sub]
      _ ≤ ((0 + ε : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr this
  have hzj : z j ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (by simpa using hz j)
  have hkey := le_of_eventually_le_on_unitSphere hsub (C := 0) hbd (z j) hzj
  rw [coordinateSlice_self] at hkey
  have : ((w z - H (z j) : ℝ) : EReal) ≤ ((0 : ℝ) : EReal) := by
    rw [EReal.coe_sub]
    simpa using hkey
  have := EReal.coe_le_coe_iff.mp this
  linarith

/-- A competitor is bounded above by any upper bound for the data on `PBar`. -/
theorem IsPerronCompetitor.le_of_forall_le {v w : ComplexModel n → ℝ}
    (hw : IsPerronCompetitor v w) {M : ℝ}
    (hv : ∀ x ∈ closedUnitPolydisk n, v x ≤ M) {z : ComplexModel n}
    (hz : z ∈ unitPolydisk n) (j : Fin n) : w z ≤ M := by
  have hH : HarmonicOnNhd (fun _ : ℂ => M) univ := by
    have h0 := harmonicOnNhd_affine_re (a := (M : ℂ)) (b := 0)
    have heq : (fun μ : ℂ => (((M : ℂ)) + 0 * μ).re) = fun _ : ℂ => M := by
      funext μ; simp
    rwa [heq] at h0
  refine hw.le_harmonic hz j hH ?_
  intro μ hμ
  exact hv _ (coordinateSlice_mem_closedUnitPolydisk
    (unitPolydisk_subset_closedUnitPolydisk hz) hμ.le)

/-- On the unit circle, `2 - 2 Re(μ conj c) = ‖μ - c‖²` for `‖c‖ = 1`. -/
theorem two_sub_two_re_mul_conj {μ c : ℂ} (hμ : ‖μ‖ = 1) (hc : ‖c‖ = 1) :
    2 - 2 * (μ * (starRingEnd ℂ) c).re = ‖μ - c‖ ^ 2 := by
  have h := Complex.normSq_sub μ c
  have h1 : Complex.normSq μ = 1 := by
    rw [Complex.normSq_eq_norm_sq, hμ]; norm_num
  have h2 : Complex.normSq c = 1 := by
    rw [Complex.normSq_eq_norm_sq, hc]; norm_num
  rw [Complex.normSq_eq_norm_sq] at h
  rw [h, h1, h2]
  ring

/-- **Uniform boundary barrier.** Near a boundary point `ζ ∈ ∂P` every
competitor is bounded above by `v ζ + ε`.  The barrier is a harmonic function
of the coordinate `z_j` for an index with `‖ζ_j‖ = 1`. -/
theorem eventually_forall_competitor_le {v : ComplexModel n → ℝ}
    (hv : ContinuousOn v (closedUnitPolydisk n)) {M : ℝ}
    (hM : ∀ x ∈ closedUnitPolydisk n, |v x| ≤ M)
    {ζ : ComplexModel n} (hζ : ζ ∈ closedUnitPolydisk n \ unitPolydisk n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 ζ, ∀ w : ComplexModel n → ℝ, IsPerronCompetitor v w →
      z ∈ unitPolydisk n → w z ≤ v ζ + ε := by
  obtain ⟨j, hj⟩ := exists_norm_eq_one_of_mem_boundary hζ
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM ζ hζ.1)
  obtain ⟨ρ, hρ, hρv⟩ := Metric.continuousWithinAt_iff.mp (hv ζ hζ.1) (ε / 2) (by linarith)
  set K : ℝ := 8 * M / ρ ^ 2 + 1 with hK
  have hKpos : 0 < K := by positivity
  set H : ℂ → ℝ := fun μ => v ζ + ε / 2 + K * (2 - 2 * (μ * (starRingEnd ℂ) (ζ j)).re)
    with hHdef
  have hHharm : HarmonicOnNhd H univ := by
    have heq : H = fun μ : ℂ => (((v ζ + ε / 2 + 2 * K : ℝ) : ℂ) +
        ((-2 * K : ℝ) : ℂ) * (starRingEnd ℂ) (ζ j) * μ).re := by
      funext μ
      simp only [hHdef, Complex.add_re, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
      ring
    rw [heq]
    exact harmonicOnNhd_affine_re _ _
  have hbarrier : ∀ z ∈ unitPolydisk n, ‖z - ζ‖ < ρ / 4 →
      ∀ w : ComplexModel n → ℝ, IsPerronCompetitor v w → w z ≤ H (z j) := by
    intro z hz hzρ w hw
    refine hw.le_harmonic hz j hHharm ?_
    intro μ hμ
    have hx : coordinateSlice z j μ ∈ closedUnitPolydisk n :=
      coordinateSlice_mem_closedUnitPolydisk
        (unitPolydisk_subset_closedUnitPolydisk hz) hμ.le
    have hsq : 2 - 2 * (μ * (starRingEnd ℂ) (ζ j)).re = ‖μ - ζ j‖ ^ 2 :=
      two_sub_two_re_mul_conj hμ hj
    by_cases hcase : ‖μ - ζ j‖ < ρ / 2
    · have hdist : ‖coordinateSlice z j μ - ζ‖ < ρ := by
        have := norm_coordinateSlice_sub_le z ζ j μ
        linarith
      have := hρv hx (by rw [dist_eq_norm]; exact hdist)
      rw [Real.dist_eq] at this
      have hle : v (coordinateSlice z j μ) ≤ v ζ + ε / 2 := by
        have := abs_lt.mp this
        linarith [this.2]
      have hnn : 0 ≤ K * (2 - 2 * (μ * (starRingEnd ℂ) (ζ j)).re) := by
        rw [hsq]; positivity
      simp only [hHdef]
      linarith
    · push Not at hcase
      have hbig : 2 * M ≤ K * (2 - 2 * (μ * (starRingEnd ℂ) (ζ j)).re) := by
        rw [hsq]
        have hsq2 : ρ ^ 2 / 4 ≤ ‖μ - ζ j‖ ^ 2 := by nlinarith [norm_nonneg (μ - ζ j)]
        have h8 : 8 * M / ρ ^ 2 ≤ K := by rw [hK]; linarith
        have hstep : (8 * M / ρ ^ 2) * (ρ ^ 2 / 4) ≤ K * ‖μ - ζ j‖ ^ 2 :=
          mul_le_mul h8 hsq2 (by positivity) hKpos.le
        have hval : (8 * M / ρ ^ 2) * (ρ ^ 2 / 4) = 2 * M := by
          field_simp
          ring
        linarith
      have h1 : v (coordinateSlice z j μ) ≤ M := le_trans (le_abs_self _) (hM _ hx)
      have h2 : -M ≤ v ζ := by
        have := hM ζ hζ.1
        have := abs_le.mp this
        linarith [this.1]
      simp only [hHdef]
      linarith
  have hnear : ∀ᶠ z : ComplexModel n in 𝓝 ζ, ‖z - ζ‖ < ρ / 4 := by
    have : ∀ᶠ z : ComplexModel n in 𝓝 ζ, dist z ζ < ρ / 4 :=
      Metric.eventually_nhds_iff.mpr ⟨ρ / 4, by linarith, fun _ hy => hy⟩
    filter_upwards [this] with z hz
    rwa [dist_eq_norm] at hz
  have hHz : ∀ᶠ z : ComplexModel n in 𝓝 ζ, H (z j) ≤ v ζ + ε := by
    have hcont : ContinuousAt (fun z : ComplexModel n => H (z j)) ζ := by
      simp only [hHdef]
      fun_prop
    have hval : H (ζ j) = v ζ + ε / 2 := by
      have hzero : 2 - 2 * (ζ j * (starRingEnd ℂ) (ζ j)).re = 0 := by
        have := two_sub_two_re_mul_conj hj hj
        simpa using this
      simp only [hHdef, hzero]
      ring
    have hlt : H (ζ j) < v ζ + ε := by rw [hval]; linarith
    have hnhds : ∀ᶠ y : ℝ in 𝓝 (H (ζ j)), y < v ζ + ε := eventually_lt_nhds hlt
    exact (hcont.eventually hnhds).mono fun z hz => hz.le
  filter_upwards [hnear, hHz] with z hz hHz' w hw hzP
  exact (hbarrier z hzP hz w hw).trans hHz'

/-! ### Admissible boundary data and the envelope -/

/-- Boundary data for the Dirichlet problem on the unit polydisk: a function
continuous on `PBar` and plurisubharmonic on `P`.  The dimension is positive, so
that the polydisk has a nonempty boundary and the envelope is finite. -/
structure IsPerronData (v : ComplexModel n → ℝ) : Prop where
  pos : 0 < n
  continuousOn : ContinuousOn v (closedUnitPolydisk n)
  psh : PlurisubharmonicOn (fun z => (v z : EReal)) (unitPolydisk n)

theorem IsPerronData.exists_bound {v : ComplexModel n → ℝ} (hv : IsPerronData v) :
    ∃ M : ℝ, ∀ x ∈ closedUnitPolydisk n, |v x| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_closedUnitPolydisk.exists_bound_of_continuousOn hv.continuousOn
  exact ⟨M, fun x hx => by simpa [Real.norm_eq_abs] using hM x hx⟩

/-- The data itself is a competitor. -/
theorem IsPerronData.isPerronCompetitor_self {v : ComplexModel n → ℝ}
    (hv : IsPerronData v) : IsPerronCompetitor v v := by
  refine ⟨hv.psh, ?_⟩
  intro ζ hζ ε hε
  have hcw : ContinuousWithinAt v (closedUnitPolydisk n) ζ := hv.continuousOn ζ hζ.1
  have hev : ∀ᶠ z in 𝓝[closedUnitPolydisk n] ζ, v z ≤ v ζ + ε := by
    have := hcw.tendsto.eventually (eventually_lt_nhds (show v ζ < v ζ + ε by linarith))
    exact this.mono fun z hz => hz.le
  exact nhdsWithin_mono ζ unitPolydisk_subset_closedUnitPolydisk hev

/-- The Perron–Bremermann envelope of the boundary data `v` on the unit
polydisk. -/
def perronEnvelope (v : ComplexModel n → ℝ) (z : ComplexModel n) : ℝ :=
  ⨆ w : {w : ComplexModel n → ℝ // IsPerronCompetitor v w}, w.1 z

theorem IsPerronData.bddAbove_competitors {v : ComplexModel n → ℝ}
    (hv : IsPerronData v) {M : ℝ} (hM : ∀ x ∈ closedUnitPolydisk n, v x ≤ M)
    {z : ComplexModel n} (hz : z ∈ unitPolydisk n) :
    BddAbove (range fun w : {w : ComplexModel n → ℝ // IsPerronCompetitor v w} => w.1 z) := by
  refine ⟨M, ?_⟩
  rintro y ⟨w, rfl⟩
  exact w.2.le_of_forall_le hM hz ⟨0, hv.pos⟩

/-- Every competitor lies below the envelope. -/
theorem IsPerronData.le_perronEnvelope {v w : ComplexModel n → ℝ}
    (hv : IsPerronData v) (hw : IsPerronCompetitor v w) {z : ComplexModel n}
    (hz : z ∈ unitPolydisk n) : w z ≤ perronEnvelope v z := by
  obtain ⟨M, hM⟩ := hv.exists_bound
  have hM' : ∀ x ∈ closedUnitPolydisk n, v x ≤ M :=
    fun x hx => le_trans (le_abs_self _) (hM x hx)
  exact le_ciSup (f := fun w : {w : ComplexModel n → ℝ // IsPerronCompetitor v w} => w.1 z)
    (hv.bddAbove_competitors hM' hz) ⟨w, hw⟩

/-- The data lies below its envelope. -/
theorem IsPerronData.self_le_perronEnvelope {v : ComplexModel n → ℝ}
    (hv : IsPerronData v) {z : ComplexModel n} (hz : z ∈ unitPolydisk n) :
    v z ≤ perronEnvelope v z :=
  hv.le_perronEnvelope hv.isPerronCompetitor_self hz

/-- The envelope inherits every upper bound of the data on `PBar`. -/
theorem IsPerronData.perronEnvelope_le_of_forall_le {v : ComplexModel n → ℝ}
    (hv : IsPerronData v) {M : ℝ} (hM : ∀ x ∈ closedUnitPolydisk n, v x ≤ M)
    {z : ComplexModel n} (hz : z ∈ unitPolydisk n) : perronEnvelope v z ≤ M := by
  have : Nonempty {w : ComplexModel n → ℝ // IsPerronCompetitor v w} :=
    ⟨⟨v, hv.isPerronCompetitor_self⟩⟩
  exact ciSup_le fun w => w.2.le_of_forall_le hM hz ⟨0, hv.pos⟩

/-- The envelope satisfies the boundary estimate defining the competitor
class. -/
theorem IsPerronData.eventually_perronEnvelope_le {v : ComplexModel n → ℝ}
    (hv : IsPerronData v) {ζ : ComplexModel n}
    (hζ : ζ ∈ closedUnitPolydisk n \ unitPolydisk n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝[unitPolydisk n] ζ, perronEnvelope v z ≤ v ζ + ε := by
  have : Nonempty {w : ComplexModel n → ℝ // IsPerronCompetitor v w} :=
    ⟨⟨v, hv.isPerronCompetitor_self⟩⟩
  obtain ⟨M, hM⟩ := hv.exists_bound
  have hbar := eventually_forall_competitor_le hv.continuousOn hM hζ hε
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hbar] with z hzP hzbar
  exact ciSup_le fun w => hzbar w.1 w.2 hzP

/-! ### Plurisubharmonicity and maximality of the envelope -/

/-- The competitor family, viewed as a family of `EReal`-valued functions. -/
def perronFamily (v : ComplexModel n → ℝ) : Set (ComplexModel n → EReal) :=
  {f | ∃ w : ComplexModel n → ℝ, IsPerronCompetitor v w ∧ f = fun z => (w z : EReal)}

theorem le_sSup_perronFamily {v w : ComplexModel n → ℝ} (hw : IsPerronCompetitor v w)
    (z : ComplexModel n) : (w z : EReal) ≤ sSup (perronFamily v) z := by
  have hmem : (fun y => (w y : EReal)) ∈ perronFamily v := ⟨w, hw, rfl⟩
  exact (le_sSup hmem : (fun y => (w y : EReal)) ≤ sSup (perronFamily v)) z

theorem sSup_perronFamily_apply_le {v : ComplexModel n → ℝ} {C : ℝ}
    {z : ComplexModel n}
    (h : ∀ w : ComplexModel n → ℝ, IsPerronCompetitor v w → w z ≤ C) :
    sSup (perronFamily v) z ≤ (C : EReal) := by
  rw [sSup_apply]
  refine iSup_le ?_
  rintro ⟨f, w, hw, rfl⟩
  exact EReal.coe_le_coe_iff.mpr (h w hw)

/-- **The envelope is a competitor.**  Its upper-semicontinuous regularization
is plurisubharmonic on `P` and still satisfies the boundary estimate, hence is a
competitor; it therefore lies below the envelope, which forces the two to agree
on `P`. -/
theorem IsPerronData.isPerronCompetitor_perronEnvelope {v : ComplexModel n → ℝ}
    (hv : IsPerronData v) : IsPerronCompetitor v (perronEnvelope v) := by
  obtain ⟨M, hM⟩ := hv.exists_bound
  have hMle : ∀ x ∈ closedUnitPolydisk n, v x ≤ M :=
    fun x hx => (le_abs_self _).trans (hM x hx)
  have hne : Nonempty {w : ComplexModel n → ℝ // IsPerronCompetitor v w} :=
    ⟨⟨v, hv.isPerronCompetitor_self⟩⟩
  have hFne : (perronFamily v).Nonempty := ⟨_, ⟨v, hv.isPerronCompetitor_self, rfl⟩⟩
  have hFpsh : ∀ f ∈ perronFamily v, PlurisubharmonicOn f (unitPolydisk n) := by
    rintro f ⟨w, hw, rfl⟩
    exact hw.1
  have hFbdd : LocallyUniformlyBoundedAbove (perronFamily v) (unitPolydisk n) := by
    intro x hx
    refine ⟨univ, univ_mem, M, ?_⟩
    rintro f ⟨w, hw, rfl⟩ y ⟨-, hy⟩
    exact EReal.coe_le_coe_iff.mpr (hw.le_of_forall_le hMle hy ⟨0, hv.pos⟩)
  set g : ComplexModel n → EReal := uscRegularization (sSup (perronFamily v)) with hgdef
  have hgpsh : PlurisubharmonicOn g (unitPolydisk n) :=
    plurisubharmonicOn_uscRegularization_sSup isOpen_unitPolydisk hFne hFpsh hFbdd
  have hgle : ∀ z ∈ unitPolydisk n, g z ≤ (M : EReal) := by
    intro z hz
    refine uscRegularization_le_of_eventually_le upperSemicontinuousAt_const ?_
    filter_upwards [isOpen_unitPolydisk.mem_nhds hz] with y hy
    exact sSup_perronFamily_apply_le fun w hw => hw.le_of_forall_le hMle hy ⟨0, hv.pos⟩
  have hgge : ∀ z : ComplexModel n, (v z : EReal) ≤ g z := fun z =>
    (le_sSup_perronFamily hv.isPerronCompetitor_self z).trans
      (le_uscRegularization (sSup (perronFamily v)) z)
  set G : ComplexModel n → ℝ := fun z => (g z).toReal with hGdef
  have hGcoe : ∀ z ∈ unitPolydisk n, ((G z : ℝ) : EReal) = g z := by
    intro z hz
    refine EReal.coe_toReal ?_ ?_
    · exact ne_of_lt (lt_of_le_of_lt (hgle z hz) (EReal.coe_lt_top M))
    · exact ne_bot_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe (v z)) (hgge z))
  have hGcomp : IsPerronCompetitor v G := by
    refine ⟨?_, ?_⟩
    · intro z hz
      refine (hgpsh z hz).congr ?_
      filter_upwards [isOpen_unitPolydisk.mem_nhds hz] with y hy
      exact (hGcoe y hy).symm
    · intro ζ hζ ε hε
      obtain ⟨U, hUsub, hUopen, hζU⟩ :=
        _root_.mem_nhds_iff.mp (eventually_forall_competitor_le hv.continuousOn hM hζ hε)
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hUopen.mem_nhds hζU)]
        with z hzP hzU
      have hnbhd : U ∩ unitPolydisk n ∈ 𝓝 z :=
        (hUopen.inter isOpen_unitPolydisk).mem_nhds ⟨hzU, hzP⟩
      have hgz : g z ≤ ((v ζ + ε : ℝ) : EReal) := by
        refine uscRegularization_le_of_eventually_le upperSemicontinuousAt_const ?_
        filter_upwards [hnbhd] with y hy
        exact sSup_perronFamily_apply_le fun w hw => hUsub hy.1 w hw hy.2
      rw [← hGcoe z hzP] at hgz
      exact EReal.coe_le_coe_iff.mp hgz
  have hleG : ∀ z ∈ unitPolydisk n, perronEnvelope v z ≤ G z := by
    intro z hz
    refine ciSup_le fun w => ?_
    have h1 : ((w.1 z : ℝ) : EReal) ≤ g z :=
      (le_sSup_perronFamily w.2 z).trans (le_uscRegularization _ z)
    rw [← hGcoe z hz] at h1
    exact EReal.coe_le_coe_iff.mp h1
  have heq : ∀ z ∈ unitPolydisk n, perronEnvelope v z = G z := fun z hz =>
    le_antisymm (hleG z hz) (hv.le_perronEnvelope hGcomp hz)
  refine ⟨?_, fun ζ hζ ε hε => hv.eventually_perronEnvelope_le hζ hε⟩
  intro z hz
  refine (hGcomp.1 z hz).congr ?_
  filter_upwards [isOpen_unitPolydisk.mem_nhds hz] with y hy
  exact congrArg _ (heq y hy).symm

/-- The envelope is plurisubharmonic on the open polydisk. -/
theorem IsPerronData.plurisubharmonicOn_perronEnvelope {v : ComplexModel n → ℝ}
    (hv : IsPerronData v) :
    PlurisubharmonicOn (fun z => (perronEnvelope v z : EReal)) (unitPolydisk n) :=
  hv.isPerronCompetitor_perronEnvelope.1

/-- **The envelope is maximal.**  If `w` is plurisubharmonic on `P` and lies
below the envelope off a compact subset, then `max (w, u)` is again a
competitor, so `w ≤ u` everywhere on `P`. -/
theorem IsPerronData.isMaximalPshOn_perronEnvelope {v : ComplexModel n → ℝ}
    (hv : IsPerronData v) :
    IsMaximalPshOn ⟨unitPolydisk n, isOpen_unitPolydisk⟩ (perronEnvelope v) := by
  refine ⟨hv.plurisubharmonicOn_perronEnvelope, ?_⟩
  intro w hw K hK hKP hle z hz
  set G : ComplexModel n → ℝ := fun y => max (w y) (perronEnvelope v y) with hGdef
  have hcoe : ∀ y : ComplexModel n,
      ((G y : ℝ) : EReal) = max ((w y : EReal)) ((perronEnvelope v y : EReal)) := by
    intro y
    rcases le_total (w y) (perronEnvelope v y) with h | h
    · rw [hGdef]
      simp [max_eq_right h, max_eq_right (EReal.coe_le_coe_iff.mpr h)]
    · rw [hGdef]
      simp [max_eq_left h, max_eq_left (EReal.coe_le_coe_iff.mpr h)]
  have hGcomp : IsPerronCompetitor v G := by
    refine ⟨?_, ?_⟩
    · have hmax := hw.max hv.plurisubharmonicOn_perronEnvelope
      intro y hy
      refine (hmax y hy).congr ?_
      exact Filter.Eventually.of_forall fun x => (hcoe x).symm
    · intro ζ hζ ε hε
      have hKc : Kᶜ ∈ 𝓝 ζ :=
        hK.isClosed.isOpen_compl.mem_nhds fun hmem => hζ.2 (hKP hmem)
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hKc,
        hv.eventually_perronEnvelope_le hζ hε] with y hyP hyK hyenv
      have hwy : w y ≤ perronEnvelope v y := hle y ⟨hyP, hyK⟩
      rw [hGdef]
      exact max_le (hwy.trans hyenv) hyenv
  exact le_trans (le_max_left _ _) (hv.le_perronEnvelope hGcomp hz)

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
