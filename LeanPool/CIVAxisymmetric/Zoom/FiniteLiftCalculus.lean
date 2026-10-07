/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Zoom.FiniteAxisBounds
public import LeanPool.CIVAxisymmetric.Statements.DtPast
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Derivatives of functions lifted through `(X, Z, τ) ↦ (|X|, Z, τ)`

A function `g` of the meridional variables `((R, Z), τ)` is lifted to the variables
`(X, Z, τ) ∈ ℝ⁴ × ℝ × ℝ` of `eq:aniso:zoom:lifted` by composing with `zoomLiftPoint`. Off the axis
`X = 0` the lift is differentiable, and its derivatives in the coordinate directions are
`∂_{X_i} (g ∘ L) = ∂_R g · X_i / R`, `∂_Z (g ∘ L) = ∂_Z g`, `∂_τ (g ∘ L) = ∂_τ g`
(`fderiv_comp_zoomLiftPoint_radial`, `fderiv_comp_zoomLiftPoint_vertical`,
`fderiv_comp_zoomLiftPoint_time`). The derivative of `G ∘ L · X_i / R` in the direction `X_i`
is `∂_R G · X_i² / R² + G · (1 / R - X_i² / R³)` (`fderiv_comp_zoomLiftPoint_mul_dir`); summed
over the four radial directions this produces the radial operator `∂_RR + 3 R⁻¹ ∂_R` of
`eq:aniso:zoom:finite:equation` and the divergence `∂_R V + 3 V / R + ∂_Z W` of the drift of
`eq:drift:Bn:def`.
-/

public section

open Set Filter Topology
open CKN

noncomputable section
namespace CIV

/-! ### Meridional slices -/

/-- The radial slice of a differentiable function has derivative `dr`. -/
theorem hasDerivAt_dr_of_differentiableAt {G : (ℝ × ℝ) × ℝ → ℝ} {p : (ℝ × ℝ) × ℝ}
    (hG : DifferentiableAt ℝ G p) : HasDerivAt (fun r => G ((r, p.1.2), p.2)) (dr G p) p.1.1 := by
  have hc : HasDerivAt (fun r : ℝ => ((r, p.1.2), p.2)) (((1 : ℝ), (0 : ℝ)), (0 : ℝ)) p.1.1 :=
    ((hasDerivAt_id _).prodMk (hasDerivAt_const _ _)).prodMk (hasDerivAt_const _ _)
  have hG' : DifferentiableAt ℝ G ((p.1.1, p.1.2), p.2) := hG
  exact (hG'.hasFDerivAt.comp_hasDerivAt p.1.1 hc).differentiableAt.hasDerivAt

/-- The vertical slice of a differentiable function has derivative `dz`. -/
theorem hasDerivAt_dz_of_differentiableAt {G : (ℝ × ℝ) × ℝ → ℝ} {p : (ℝ × ℝ) × ℝ}
    (hG : DifferentiableAt ℝ G p) : HasDerivAt (fun z => G ((p.1.1, z), p.2)) (dz G p) p.1.2 := by
  have hc : HasDerivAt (fun z : ℝ => ((p.1.1, z), p.2)) (((0 : ℝ), (1 : ℝ)), (0 : ℝ)) p.1.2 :=
    ((hasDerivAt_const _ _).prodMk (hasDerivAt_id _)).prodMk (hasDerivAt_const _ _)
  have hG' : DifferentiableAt ℝ G ((p.1.1, p.1.2), p.2) := hG
  exact (hG'.hasFDerivAt.comp_hasDerivAt p.1.2 hc).differentiableAt.hasDerivAt

/-- The time slice of a differentiable function has derivative `dtPast`. -/
theorem hasDerivAt_dtPast_of_differentiableAt {G : (ℝ × ℝ) × ℝ → ℝ} {p : (ℝ × ℝ) × ℝ}
    (hG : DifferentiableAt ℝ G p) : HasDerivAt (fun t => G (p.1, t)) (dtPast G p) p.2 := by
  have hc : HasDerivAt (fun t : ℝ => (p.1, t)) (((0 : ℝ), (0 : ℝ)), (1 : ℝ)) p.2 :=
    (hasDerivAt_const _ _).prodMk (hasDerivAt_id _)
  have hG' : DifferentiableAt ℝ G (p.1, p.2) := hG
  have hd := (hG'.hasFDerivAt.comp_hasDerivAt p.2 hc).differentiableAt.hasDerivAt
  have hw : dtPast G p = deriv (fun t => G (p.1, t)) p.2 :=
    hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic _)
  rw [hw]
  exact hd

/-- `dr` of a differentiable function is its derivative in the direction `((1, 0), 0)`. -/
theorem dr_eq_fderiv {G : (ℝ × ℝ) × ℝ → ℝ} {p : (ℝ × ℝ) × ℝ} (hG : DifferentiableAt ℝ G p) :
    dr G p = fderiv ℝ G p (((1 : ℝ), (0 : ℝ)), (0 : ℝ)) := by
  have hc : HasDerivAt (fun r : ℝ => ((r, p.1.2), p.2)) (((1 : ℝ), (0 : ℝ)), (0 : ℝ)) p.1.1 :=
    ((hasDerivAt_id _).prodMk (hasDerivAt_const _ _)).prodMk (hasDerivAt_const _ _)
  have hG' : DifferentiableAt ℝ G ((p.1.1, p.1.2), p.2) := hG
  exact (hasDerivAt_dr_of_differentiableAt hG).unique (hG'.hasFDerivAt.comp_hasDerivAt p.1.1 hc)

/-- `dz` of a differentiable function is its derivative in the direction `((0, 1), 0)`. -/
theorem dz_eq_fderiv {G : (ℝ × ℝ) × ℝ → ℝ} {p : (ℝ × ℝ) × ℝ} (hG : DifferentiableAt ℝ G p) :
    dz G p = fderiv ℝ G p (((0 : ℝ), (1 : ℝ)), (0 : ℝ)) := by
  have hc : HasDerivAt (fun z : ℝ => ((p.1.1, z), p.2)) (((0 : ℝ), (1 : ℝ)), (0 : ℝ)) p.1.2 :=
    ((hasDerivAt_const _ _).prodMk (hasDerivAt_id _)).prodMk (hasDerivAt_const _ _)
  have hG' : DifferentiableAt ℝ G ((p.1.1, p.1.2), p.2) := hG
  exact (hasDerivAt_dz_of_differentiableAt hG).unique (hG'.hasFDerivAt.comp_hasDerivAt p.1.2 hc)

/-- `dr` of a function smooth on an open set is smooth there. -/
theorem contDiffOn_dr {G : (ℝ × ℝ) × ℝ → ℝ} {O : Set ((ℝ × ℝ) × ℝ)} (hO : IsOpen O)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G O) : ContDiffOn ℝ (⊤ : ℕ∞) (dr G) O := by
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ G p (((1 : ℝ), (0 : ℝ)), (0 : ℝ))) O :=
    (hG.fderiv_of_isOpen hO (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffOn_const
  refine hF.congr fun p hp => ?_
  exact dr_eq_fderiv ((hG.differentiableOn (by simp) p hp).differentiableAt (hO.mem_nhds hp))

/-- `dz` of a function smooth on an open set is smooth there. -/
theorem contDiffOn_dz {G : (ℝ × ℝ) × ℝ → ℝ} {O : Set ((ℝ × ℝ) × ℝ)} (hO : IsOpen O)
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G O) : ContDiffOn ℝ (⊤ : ℕ∞) (dz G) O := by
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ G p (((0 : ℝ), (1 : ℝ)), (0 : ℝ))) O :=
    (hG.fderiv_of_isOpen hO (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffOn_const
  refine hF.congr fun p hp => ?_
  exact dz_eq_fderiv ((hG.differentiableOn (by simp) p hp).differentiableAt (hO.mem_nhds hp))

/-- A directional derivative is the derivative along the line. -/
theorem fderiv_apply_eq_of_hasDerivAt_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {z v : E} {D : ℝ} (hf : DifferentiableAt ℝ f z)
    (hD : HasDerivAt (fun t : ℝ => f (z + t • v)) D 0) : fderiv ℝ f z v = D :=
  HasDerivAt.unique (hf.hasFDerivAt.hasLineDerivAt v) hD

/-! ### The one-variable core -/

/-- The chain rule through `b ↦ √(b² + c)`. -/
theorem hasDerivAt_comp_sqrt_sq_add {G : ℝ → ℝ} {G' c a r : ℝ} (hpos : 0 < a ^ 2 + c)
    (hr : r = Real.sqrt (a ^ 2 + c)) (hG : HasDerivAt G G' r) :
    HasDerivAt (fun b => G (Real.sqrt (b ^ 2 + c))) (G' * (a / r)) a := by
  subst hr
  exact hG.comp a (hasDerivAt_sqrt_sq_add hpos)

/-- The derivative of `b ↦ G(√(b² + c)) · b / √(b² + c)`. -/
theorem hasDerivAt_comp_sqrt_sq_add_mul_div {G : ℝ → ℝ} {G' c a r : ℝ} (hpos : 0 < a ^ 2 + c)
    (hr : r = Real.sqrt (a ^ 2 + c)) (hG : HasDerivAt G G' r) :
    HasDerivAt (fun b => G (Real.sqrt (b ^ 2 + c)) * (b / Real.sqrt (b ^ 2 + c)))
      (G' * (a / r) ^ 2 + G r * (1 / r - a ^ 2 / r ^ 3)) a := by
  have h1 := hasDerivAt_comp_sqrt_sq_add hpos hr hG
  have hs := hasDerivAt_sqrt_sq_add hpos
  have hne : Real.sqrt (a ^ 2 + c) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have h2 := (hasDerivAt_id' a).fun_div hs hne
  have h3 := h1.fun_mul h2
  subst hr
  convert h3 using 1
  field_simp

/-! ### The lift -/

/-- The lift is differentiable off the axis. -/
theorem differentiableAt_zoomLiftRadius {z : Vec 5 × ℝ} (hR : 0 < zoomLiftRadius z.1) :
    DifferentiableAt ℝ (fun w : Vec 5 × ℝ => zoomLiftRadius w.1) z := by
  have hs : z.1 0 ^ 2 + z.1 1 ^ 2 + z.1 2 ^ 2 + z.1 3 ^ 2 ≠ 0 := by
    intro h0
    rw [zoomLiftRadius, h0, Real.sqrt_zero] at hR
    exact lt_irrefl 0 hR
  unfold zoomLiftRadius
  refine DifferentiableAt.sqrt ?_ hs
  fun_prop

/-- The lift is differentiable off the axis. -/
theorem differentiableAt_zoomLiftPoint {z : Vec 5 × ℝ} (hR : 0 < zoomLiftRadius z.1) :
    DifferentiableAt ℝ zoomLiftPoint z := by
  have h1 := differentiableAt_zoomLiftRadius hR
  have h2 : DifferentiableAt ℝ (fun w : Vec 5 × ℝ => w.1 4) z := by fun_prop
  have h3 : DifferentiableAt ℝ (fun w : Vec 5 × ℝ => w.2) z := differentiableAt_snd
  exact (h1.prodMk h2).prodMk h3

/-- The lift is smooth off the axis. -/
theorem contDiffOn_zoomLiftPoint :
    ContDiffOn ℝ (⊤ : ℕ∞) zoomLiftPoint {z : Vec 5 × ℝ | 0 < zoomLiftRadius z.1} := by
  intro z hz
  have hs : z.1 0 ^ 2 + z.1 1 ^ 2 + z.1 2 ^ 2 + z.1 3 ^ 2 ≠ 0 := by
    intro h0
    have hR : 0 < zoomLiftRadius z.1 := hz
    rw [zoomLiftRadius, h0, Real.sqrt_zero] at hR
    exact lt_irrefl 0 hR
  have hR : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : Vec 5 × ℝ => zoomLiftRadius w.1) z := by
    unfold zoomLiftRadius
    refine ContDiffAt.sqrt ?_ hs
    fun_prop
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : Vec 5 × ℝ => w.1 4) z := by fun_prop
  have h3 : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : Vec 5 × ℝ => w.2) z := contDiffAt_snd
  exact ((hR.prodMk h2).prodMk h3).contDiffWithinAt

/-- Moving along a radial coordinate direction. -/
theorem zoomLiftPoint_add_smul_radial {z : Vec 5 × ℝ} {i : Fin 5} (hi : i ≠ 4) {c : ℝ}
    (hc : ∀ s : ℝ, zoomLiftRadius (Function.update z.1 i s) = Real.sqrt (s ^ 2 + c)) (t : ℝ) :
    zoomLiftPoint (z + t • ((basisVec i, 0) : Vec 5 × ℝ))
      = ((Real.sqrt ((z.1 i + t) ^ 2 + c), z.1 4), z.2) := by
  have hX : (z + t • ((basisVec i, 0) : Vec 5 × ℝ)).1 = Function.update z.1 i (z.1 i + t) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  have h4 : (4 : Fin 5) ≠ i := fun h => hi h.symm
  simp only [zoomLiftPoint, hX, hc]
  simp [h4]

/-- Moving along the vertical coordinate direction. -/
theorem zoomLiftPoint_add_smul_vertical (z : Vec 5 × ℝ) (t : ℝ) :
    zoomLiftPoint (z + t • ((basisVec 4, 0) : Vec 5 × ℝ))
      = ((zoomLiftRadius z.1, z.1 4 + t), z.2) := by
  simp [zoomLiftPoint, zoomLiftRadius]

/-- Moving in time. -/
theorem zoomLiftPoint_add_smul_time (z : Vec 5 × ℝ) (t : ℝ) :
    zoomLiftPoint (z + t • (((0 : Vec 5), (1 : ℝ)) : Vec 5 × ℝ))
      = ((zoomLiftRadius z.1, z.1 4), z.2 + t) := by
  simp [zoomLiftPoint]

/-- `∂_{X_i} (g ∘ L) = ∂_R g · X_i / R` off the axis. -/
theorem fderiv_comp_zoomLiftPoint_radial {g : (ℝ × ℝ) × ℝ → ℝ} {z : Vec 5 × ℝ}
    (hR : 0 < zoomLiftRadius z.1) (hg : DifferentiableAt ℝ g (zoomLiftPoint z)) {i : Fin 5}
    (hi : i ≠ 4) :
    fderiv ℝ (fun w => g (zoomLiftPoint w)) z (basisVec i, 0)
      = dr g (zoomLiftPoint z) * (z.1 i / zoomLiftRadius z.1) := by
  obtain ⟨c, hc0, hc⟩ := exists_zoomLiftRadius_update z.1 hi
  have hRz : zoomLiftRadius z.1 = Real.sqrt (z.1 i ^ 2 + c) := by
    rw [← hc, Function.update_eq_self]
  have hpos : 0 < z.1 i ^ 2 + c := by
    rcases (sq_nonneg (z.1 i)).lt_or_eq with h | h
    · linarith only [h, hc0]
    · rw [← h, zero_add]
      rcases hc0.lt_or_eq with h' | h'
      · exact h'
      · rw [hRz, ← h, ← h', add_zero, Real.sqrt_zero] at hR
        exact absurd hR (lt_irrefl 0)
  have hs : HasDerivAt (fun r => g ((r, z.1 4), z.2)) (dr g (zoomLiftPoint z))
      (zoomLiftRadius z.1) := hasDerivAt_dr_of_differentiableAt hg
  have h1 := hasDerivAt_comp_sqrt_sq_add hpos hRz hs
  have h1' : HasDerivAt (fun t => g ((Real.sqrt ((z.1 i + t) ^ 2 + c), z.1 4), z.2))
      (dr g (zoomLiftPoint z) * (z.1 i / zoomLiftRadius z.1)) 0 := by
    have := HasDerivAt.comp_const_add (z.1 i) 0 (by rwa [add_zero])
    exact this
  refine fderiv_apply_eq_of_hasDerivAt_line (hg.comp z (differentiableAt_zoomLiftPoint hR)) ?_
  refine h1'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  simp only [zoomLiftPoint_add_smul_radial hi hc t]

/-- `∂_Z (g ∘ L) = ∂_Z g` off the axis. -/
theorem fderiv_comp_zoomLiftPoint_vertical {g : (ℝ × ℝ) × ℝ → ℝ} {z : Vec 5 × ℝ}
    (hR : 0 < zoomLiftRadius z.1) (hg : DifferentiableAt ℝ g (zoomLiftPoint z)) :
    fderiv ℝ (fun w => g (zoomLiftPoint w)) z (basisVec 4, 0) = dz g (zoomLiftPoint z) := by
  have hs : HasDerivAt (fun s => g ((zoomLiftRadius z.1, s), z.2)) (dz g (zoomLiftPoint z))
      (z.1 4) := hasDerivAt_dz_of_differentiableAt hg
  have h1 : HasDerivAt (fun t => g ((zoomLiftRadius z.1, z.1 4 + t), z.2))
      (dz g (zoomLiftPoint z)) 0 :=
    HasDerivAt.comp_const_add (z.1 4) 0 (by rwa [add_zero])
  refine fderiv_apply_eq_of_hasDerivAt_line (hg.comp z (differentiableAt_zoomLiftPoint hR)) ?_
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  simp only [zoomLiftPoint_add_smul_vertical z t]

/-- `∂_τ (g ∘ L) = ∂_τ g` off the axis. -/
theorem fderiv_comp_zoomLiftPoint_time {g : (ℝ × ℝ) × ℝ → ℝ} {z : Vec 5 × ℝ}
    (hR : 0 < zoomLiftRadius z.1) (hg : DifferentiableAt ℝ g (zoomLiftPoint z)) :
    fderiv ℝ (fun w => g (zoomLiftPoint w)) z ((0 : Vec 5), (1 : ℝ))
      = dtPast g (zoomLiftPoint z) := by
  have hs : HasDerivAt (fun s => g ((zoomLiftRadius z.1, z.1 4), s)) (dtPast g (zoomLiftPoint z))
      z.2 := hasDerivAt_dtPast_of_differentiableAt hg
  have h1 : HasDerivAt (fun t => g ((zoomLiftRadius z.1, z.1 4), z.2 + t))
      (dtPast g (zoomLiftPoint z)) 0 :=
    HasDerivAt.comp_const_add z.2 0 (by rwa [add_zero])
  refine fderiv_apply_eq_of_hasDerivAt_line (hg.comp z (differentiableAt_zoomLiftPoint hR)) ?_
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  simp only [zoomLiftPoint_add_smul_time z t]

/-- `∂_{X_i} (G ∘ L · X_i / R) = ∂_R G · X_i² / R² + G · (1 / R - X_i² / R³)` off the axis. -/
theorem fderiv_comp_zoomLiftPoint_mul_dir {G : (ℝ × ℝ) × ℝ → ℝ} {z : Vec 5 × ℝ}
    (hR : 0 < zoomLiftRadius z.1) (hG : DifferentiableAt ℝ G (zoomLiftPoint z)) {i : Fin 5}
    (hi : i ≠ 4) :
    fderiv ℝ (fun w => G (zoomLiftPoint w) * (w.1 i / zoomLiftRadius w.1)) z (basisVec i, 0)
      = dr G (zoomLiftPoint z) * (z.1 i / zoomLiftRadius z.1) ^ 2
        + G (zoomLiftPoint z) * (1 / zoomLiftRadius z.1 - z.1 i ^ 2 / zoomLiftRadius z.1 ^ 3) := by
  obtain ⟨c, hc0, hc⟩ := exists_zoomLiftRadius_update z.1 hi
  have hRz : zoomLiftRadius z.1 = Real.sqrt (z.1 i ^ 2 + c) := by
    rw [← hc, Function.update_eq_self]
  have hpos : 0 < z.1 i ^ 2 + c := by
    rcases (sq_nonneg (z.1 i)).lt_or_eq with h | h
    · linarith only [h, hc0]
    · rw [← h, zero_add]
      rcases hc0.lt_or_eq with h' | h'
      · exact h'
      · rw [hRz, ← h, ← h', add_zero, Real.sqrt_zero] at hR
        exact absurd hR (lt_irrefl 0)
  have hs : HasDerivAt (fun r => G ((r, z.1 4), z.2)) (dr G (zoomLiftPoint z))
      (zoomLiftRadius z.1) := hasDerivAt_dr_of_differentiableAt hG
  have h1 := hasDerivAt_comp_sqrt_sq_add_mul_div hpos hRz hs
  have h1' : HasDerivAt (fun t => G ((Real.sqrt ((z.1 i + t) ^ 2 + c), z.1 4), z.2)
        * ((z.1 i + t) / Real.sqrt ((z.1 i + t) ^ 2 + c)))
      (dr G (zoomLiftPoint z) * (z.1 i / zoomLiftRadius z.1) ^ 2
        + G ((zoomLiftRadius z.1, z.1 4), z.2)
          * (1 / zoomLiftRadius z.1 - z.1 i ^ 2 / zoomLiftRadius z.1 ^ 3)) 0 :=
    HasDerivAt.comp_const_add (z.1 i) 0 (by rwa [add_zero])
  have hdiff : DifferentiableAt ℝ (fun w => G (zoomLiftPoint w) * (w.1 i / zoomLiftRadius w.1))
    z := by
    refine (hG.comp z (differentiableAt_zoomLiftPoint hR)).mul ?_
    have hci : DifferentiableAt ℝ (fun w : Vec 5 × ℝ => w.1 i) z := by fun_prop
    have hRd := differentiableAt_zoomLiftRadius hR
    have hRne : zoomLiftRadius z.1 ≠ 0 := hR.ne'
    fun_prop (disch := exact hRne)
  refine fderiv_apply_eq_of_hasDerivAt_line hdiff ?_
  refine h1'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have hX : (z + t • ((basisVec i, 0) : Vec 5 × ℝ)).1 i = z.1 i + t := by simp
  have hRt : zoomLiftRadius (z + t • ((basisVec i, 0) : Vec 5 × ℝ)).1
      = Real.sqrt ((z.1 i + t) ^ 2 + c) := by
    have := zoomLiftPoint_add_smul_radial hi hc t
    exact congrArg (fun p : (ℝ × ℝ) × ℝ => p.1.1) this
  simp only [zoomLiftPoint_add_smul_radial hi hc t, hX, hRt]

end CIV
