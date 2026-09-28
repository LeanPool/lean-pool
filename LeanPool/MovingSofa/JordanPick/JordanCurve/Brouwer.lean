/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Tactic
public import LeanPool.MovingSofa.JordanPick.JordanCurve.Arcs
/-!
# Toward the 2D Brouwer fixed point theorem

We build the classical topological proof of the two-dimensional Brouwer fixed
point theorem, in four phases:

* **Phase 1** — the once-around loop on `AddCircle 1` is not homotopic (rel
  endpoints) to the constant loop.  This is the mathematical heart: it is proved
  from the covering `ℝ → AddCircle 1` via unique path lifting
  (`IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`).
* **Phase 1.5** — transport of Phase 1 across `AddCircle 1 ≃ₜ Circle ≃ₜ
  sphere (0 : ℝ²) 1` to obtain a non-nullhomotopic loop on the geometric circle.
* **Phase 2** — no retraction of the disk onto its boundary circle: a retraction
  would give a null-homotopy of the Phase 1.5 loop.
* **Phase 3** — Brouwer for the closed unit disk (`brouwer_disk`): a
  fixed-point-free self-map yields a retraction (ray construction).
* **Phase 4** — the general convex/compact/nonempty statement `brouwerFPT`.
-/

@[expose] public section

namespace JordanCurve.Brouwer

open Metric Set Function unitInterval Topology
open scoped RealInnerProductSpace

/-- The plane `ℝ²`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-! ## Phase 1 — the once-around loop on `AddCircle 1` is not nullhomotopic -/

/-- The covering map `ℝ → AddCircle 1`. -/
theorem cover : IsCoveringMap ((↑) : ℝ → AddCircle (1 : ℝ)) :=
  AddCircle.isCoveringMap_coe 1

/-- The once-around loop `t ↦ ↑t` in `AddCircle 1`. -/
noncomputable def acLoop : C(I, AddCircle (1 : ℝ)) :=
  ⟨fun t => ((t : ℝ) : AddCircle (1 : ℝ)), cover.continuous.comp continuous_subtype_val⟩

/-- The lift of `acLoop` to `ℝ` starting at `0`: the identity `t ↦ ↑t`. -/
noncomputable def idLift : C(I, ℝ) := ⟨fun t => (t : ℝ), continuous_subtype_val⟩

@[simp] lemma acLoop_apply (t : I) : acLoop t = ((t : ℝ) : AddCircle (1 : ℝ)) := rfl
@[simp] lemma idLift_apply (t : I) : idLift t = (t : ℝ) := rfl

/-- **Phase 1.** The once-around loop is not homotopic rel endpoints to the
constant loop. -/
theorem acLoop_not_homotopic :
    ¬ acLoop.HomotopicRel (ContinuousMap.const I (0 : AddCircle (1 : ℝ))) {0, 1} := by
  intro h
  have h0 : acLoop 0 = ((0 : ℝ) : AddCircle (1 : ℝ)) := by simp
  have h1 : (ContinuousMap.const I (0 : AddCircle (1 : ℝ))) 0 = ((0 : ℝ) : AddCircle (1 : ℝ)) := by
    simp
  have key := cover.liftPath_apply_one_eq_of_homotopicRel h (0 : ℝ) h0 h1
  -- Identify the two lifts.
  have e1 : cover.liftPath acLoop (0 : ℝ) h0 = idLift := by
    refine ((cover.eq_liftPath_iff' h0).mpr ⟨?_, ?_⟩).symm
    · ext t; simp
    · simp
  have e2 : cover.liftPath (ContinuousMap.const I (0 : AddCircle (1 : ℝ))) (0 : ℝ) h1
      = ContinuousMap.const I (0 : ℝ) := cover.liftPath_const h1
  rw [e1, e2] at key
  simp at key

/-! ## Phase 1.5 — transport to the geometric circle `sphere (0 : ℝ²) 1` -/

/-- The homeomorphism `AddCircle 1 ≃ₜ sphere (0 : ℝ²) 1`, via `Circle`. -/
noncomputable def acToSphere : AddCircle (1 : ℝ) ≃ₜ sphere (0 : Plane) 1 :=
  (AddCircle.homeomorphCircle (one_ne_zero)).trans Arcs.circleHomeoSphere

/-- The base point of the sphere loop. -/
noncomputable def sBase : sphere (0 : Plane) 1 := acToSphere 0

/-- The once-around loop on the geometric circle `sphere (0 : ℝ²) 1`. -/
noncomputable def sLoop : C(I, sphere (0 : Plane) 1) :=
  (⟨acToSphere, acToSphere.continuous⟩ : C(AddCircle (1 : ℝ), sphere (0 : Plane) 1)).comp acLoop

@[simp] lemma sLoop_apply (t : I) : sLoop t = acToSphere (acLoop t) := rfl

lemma sLoop_zero : sLoop 0 = sBase := by simp [sBase]

/-- **Phase 1.5.** The once-around loop on the geometric circle is not homotopic
rel endpoints to the constant loop. -/
theorem sLoop_not_homotopic :
    ¬ sLoop.HomotopicRel (ContinuousMap.const I sBase) {0, 1} := by
  intro h
  apply acLoop_not_homotopic
  have hh := h.comp_continuousMap
    (⟨acToSphere.symm, acToSphere.symm.continuous⟩ : C(sphere (0 : Plane) 1, AddCircle (1 : ℝ)))
  have e1 : (⟨acToSphere.symm, acToSphere.symm.continuous⟩ :
      C(sphere (0 : Plane) 1, AddCircle (1 : ℝ))).comp sLoop = acLoop := by
    ext t; simp [sLoop, acToSphere.symm_apply_apply]
  have e2 : (⟨acToSphere.symm, acToSphere.symm.continuous⟩ :
      C(sphere (0 : Plane) 1, AddCircle (1 : ℝ))).comp (ContinuousMap.const I sBase)
      = ContinuousMap.const I (0 : AddCircle (1 : ℝ)) := by
    ext t; simp [sBase, acToSphere.symm_apply_apply]
  rwa [e1, e2] at hh

lemma sLoop_one : sLoop 1 = sBase := by
  have : acLoop 1 = (0 : AddCircle (1 : ℝ)) := by
    simp only [acLoop_apply]
    have : ((1 : I) : ℝ) = (1 : ℝ) := rfl
    rw [this]; exact AddCircle.coe_period 1
  simp [sBase, this]

/-! ## Phase 2 — no retraction of the disk onto its boundary circle -/

/-- The straight-line contraction point `(1-t)·(loop s) + t·base` in the disk. -/
noncomputable def diskPt (t s : I) : Plane :=
  (1 - (t : ℝ)) • (sLoop s : Plane) + (t : ℝ) • (sBase : Plane)

lemma diskPt_mem (t s : I) : diskPt t s ∈ closedBall (0 : Plane) 1 := by
  have hv : (sLoop s : Plane) ∈ closedBall (0 : Plane) 1 :=
    sphere_subset_closedBall (sLoop s).2
  have hw : (sBase : Plane) ∈ closedBall (0 : Plane) 1 :=
    sphere_subset_closedBall sBase.2
  exact convex_closedBall 0 1 hv hw (by unit_interval) (by unit_interval) (by ring)

lemma continuous_diskPt : Continuous (fun p : I × I => diskPt p.1 p.2) := by
  unfold diskPt
  fun_prop

/-- The contraction as a continuous map into the disk. -/
noncomputable def diskMap : C(I × I, closedBall (0 : Plane) 1) :=
  ⟨fun p => ⟨diskPt p.1 p.2, diskPt_mem p.1 p.2⟩,
    (continuous_diskPt).subtype_mk _⟩

/-- **Phase 2.** There is no retraction of the closed disk onto its boundary
circle. -/
theorem no_retraction (ρ : C(closedBall (0 : Plane) 1, closedBall (0 : Plane) 1))
    (hrange : ∀ x, (ρ x : Plane) ∈ sphere (0 : Plane) 1)
    (hid : ∀ x : closedBall (0 : Plane) 1,
      (x : Plane) ∈ sphere (0 : Plane) 1 → (ρ x : Plane) = (x : Plane)) :
    False := by
  apply sLoop_not_homotopic
  -- The homotopy `H t s = ρ ((1-t)·loop s + t·base)`, valued in the sphere.
  set H : C(I × I, sphere (0 : Plane) 1) :=
    ⟨fun p => ⟨(ρ (diskMap p) : Plane), hrange _⟩,
      (map_continuous ρ |>.comp (map_continuous diskMap)).subtype_val.subtype_mk _⟩ with hH
  refine ⟨{
    toContinuousMap := H
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · -- H (0, s) = sLoop s
    intro s
    have hmem : (diskMap (0, s) : Plane) ∈ sphere (0 : Plane) 1 := by
      change diskPt 0 s ∈ _
      simp only [diskPt, Set.Icc.coe_zero, sub_zero, one_smul, zero_smul, add_zero]
      exact (sLoop s).2
    apply Subtype.ext
    change (ρ (diskMap (0, s)) : Plane) = (sLoop s : Plane)
    rw [hid _ hmem]
    show (diskMap (0, s) : Plane) = (sLoop s : Plane)
    change diskPt 0 s = (sLoop s : Plane)
    simp [diskPt]
  · -- H (1, s) = base
    intro s
    have hmem : (diskMap (1, s) : Plane) ∈ sphere (0 : Plane) 1 := by
      change diskPt 1 s ∈ _
      simp only [diskPt, Set.Icc.coe_one, sub_self, zero_smul, one_smul, zero_add]
      exact sBase.2
    apply Subtype.ext
    change (ρ (diskMap (1, s)) : Plane) = (sBase : Plane)
    rw [hid _ hmem]
    show (diskMap (1, s) : Plane) = (sBase : Plane)
    change diskPt 1 s = (sBase : Plane)
    simp [diskPt]
  · -- rel endpoints: for s ∈ {0,1}, H t s = sLoop s = base
    intro t s hs
    have hs' : (sLoop s : Plane) = (sBase : Plane) := by
      rcases hs with h | h
      · rw [show s = (0 : I) from h, sLoop_zero]
      · rw [show s = (1 : I) from h, sLoop_one]
    have hmem : (diskMap (t, s) : Plane) ∈ sphere (0 : Plane) 1 := by
      change diskPt t s ∈ _
      simp only [diskPt, hs', ← add_smul, sub_add_cancel, one_smul]
      exact sBase.2
    apply Subtype.ext
    change (ρ (diskMap (t, s)) : Plane) = (sLoop s : Plane)
    rw [hid _ hmem, hs']
    show (diskMap (t, s) : Plane) = (sBase : Plane)
    change diskPt t s = (sBase : Plane)
    simp only [diskPt, hs', ← add_smul, sub_add_cancel, one_smul]

/-! ## Phase 3 — Brouwer for the closed unit disk

Given a fixed-point-free self-map `f` of the disk, the ray from `f x` through `x`
exits the boundary circle at a point `ρ x`; this `ρ` is a retraction, forbidden
by Phase 2. -/

section Disk

variable (f : C(closedBall (0 : Plane) 1, closedBall (0 : Plane) 1))

/-- The direction vector `x - f x` of the ray. -/
noncomputable def dvec (x : closedBall (0 : Plane) 1) : Plane := (x : Plane) - (f x : Plane)

/-- Quadratic coefficient `A = ‖x - f x‖²`. -/
noncomputable def Acoef (x : closedBall (0 : Plane) 1) : ℝ := ⟪dvec f x, dvec f x⟫
/-- Coefficient `B = ⟪f x, x - f x⟫`. -/
noncomputable def Bcoef (x : closedBall (0 : Plane) 1) : ℝ := ⟪(f x : Plane), dvec f x⟫
/-- Coefficient `C = ‖f x‖² - 1 ≤ 0`. -/
noncomputable def Ccoef (x : closedBall (0 : Plane) 1) : ℝ := ‖(f x : Plane)‖ ^ 2 - 1
/-- Discriminant `B² - A·C ≥ 0`. -/
noncomputable def discr (x : closedBall (0 : Plane) 1) : ℝ := (Bcoef f x) ^ 2 - Acoef f x * Ccoef
  f x
/-- The (larger) root parameter `t = (-B + √disc)/A`. -/
noncomputable def tparam (x : closedBall (0 : Plane) 1) : ℝ :=
  (- Bcoef f x + Real.sqrt (discr f x)) / Acoef f x
/-- The exit point `ρ x = f x + t·(x - f x)` on the boundary circle. -/
noncomputable def rhoPt (x : closedBall (0 : Plane) 1) : Plane :=
  (f x : Plane) + tparam f x • dvec f x

variable (hf : ∀ x, (f x : Plane) ≠ (x : Plane))
include hf

lemma dvec_ne (x) : dvec f x ≠ 0 := by
  simp only [dvec, sub_ne_zero]; exact fun h => hf x h.symm

lemma Acoef_pos (x) : 0 < Acoef f x := by
  rw [Acoef, real_inner_self_eq_norm_sq]
  exact pow_pos (norm_pos_iff.mpr (dvec_ne f hf x)) 2

omit hf in
lemma Ccoef_nonpos (x) : Ccoef f x ≤ 0 := by
  rw [Ccoef, sub_nonpos]
  have : ‖(f x : Plane)‖ ≤ 1 := by
    have := (f x).2; rw [mem_closedBall, dist_zero_right] at this; exact this
  nlinarith [norm_nonneg (f x : Plane)]

lemma discr_nonneg (x) : 0 ≤ discr f x := by
  have hA := (Acoef_pos f hf x).le
  have hC := Ccoef_nonpos f x
  have : 0 ≤ Acoef f x * (- Ccoef f x) := mul_nonneg hA (by linarith)
  rw [discr]; nlinarith [sq_nonneg (Bcoef f x)]

/-- The exit point lies on the unit circle. -/
lemma norm_rhoPt (x) : ‖rhoPt f x‖ = 1 := by
  have hA := Acoef_pos f hf x
  have hsq : (Real.sqrt (discr f x)) ^ 2 = discr f x :=
    Real.sq_sqrt (discr_nonneg f hf x)
  have hnormsq : ‖rhoPt f x‖ ^ 2 = 1 := by
    rw [rhoPt, norm_add_sq_real, norm_smul, real_inner_smul_right]
    have hAe : ⟪dvec f x, dvec f x⟫ = Acoef f x := rfl
    have hBe : ⟪(f x : Plane), dvec f x⟫ = Bcoef f x := rfl
    have hCe : ‖(f x : Plane)‖ ^ 2 = Ccoef f x + 1 := by rw [Ccoef]; ring
    rw [hBe, hCe]
    have hnd : ‖dvec f x‖ ^ 2 = Acoef f x := by
      rw [← real_inner_self_eq_norm_sq]; rfl
    rw [Real.norm_eq_abs, mul_pow, sq_abs, hnd]
    -- Now: (C+1) + 2*(t*B) + t^2 * A = 1, with t = (-B+√disc)/A
    rw [tparam]
    field_simp
    rw [discr] at hsq ⊢
    nlinarith [hsq, hA]
  have := norm_nonneg (rhoPt f x)
  nlinarith [hnormsq, this]

/-- On the boundary circle, `ρ` is the identity. -/
lemma rhoPt_of_mem_sphere (x : closedBall (0 : Plane) 1)
    (hx : (x : Plane) ∈ sphere (0 : Plane) 1) :
    rhoPt f x = (x : Plane) := by
  have hxn : ‖(x : Plane)‖ = 1 := by rwa [mem_sphere_zero_iff_norm] at hx
  have hA := Acoef_pos f hf x
  have eA : Acoef f x = ‖dvec f x‖ ^ 2 := real_inner_self_eq_norm_sq _
  have eC : Ccoef f x = ‖(f x : Plane)‖ ^ 2 - 1 := rfl
  have hAdd : dvec f x + (f x : Plane) = (x : Plane) := by rw [dvec]; abel
  have hcomm : ⟪dvec f x, (f x : Plane)⟫ = Bcoef f x := by rw [Bcoef, real_inner_comm]
  have hexp : ‖(x : Plane)‖ ^ 2
      = ‖dvec f x‖ ^ 2 + 2 * ⟪dvec f x, (f x : Plane)⟫ + ‖(f x : Plane)‖ ^ 2 := by
    rw [← hAdd, norm_add_sq_real]
  rw [hxn, hcomm] at hexp
  -- A + 2B + C = 0
  have hkey : Acoef f x + 2 * Bcoef f x + Ccoef f x = 0 := by
    rw [eA, eC]; linear_combination -hexp
  -- A + B = ⟪x, x - f x⟫ = 1 - ⟪x, f x⟫ ≥ 0
  have hApB : Acoef f x + Bcoef f x = ⟪(x : Plane), dvec f x⟫ := by
    rw [Acoef, Bcoef, ← inner_add_left, hAdd]
  have hxd : ⟪(x : Plane), dvec f x⟫ = 1 - ⟪(x : Plane), (f x : Plane)⟫ := by
    rw [dvec, inner_sub_right, real_inner_self_eq_norm_sq, hxn]; norm_num
  have hcs : ⟪(x : Plane), (f x : Plane)⟫ ≤ 1 := by
    have hfn : ‖(f x : Plane)‖ ≤ 1 := by
      have := (f x).2; rwa [mem_closedBall, dist_zero_right] at this
    calc ⟪(x : Plane), (f x : Plane)⟫ ≤ ‖(x : Plane)‖ * ‖(f x : Plane)‖ := real_inner_le_norm _ _
      _ ≤ 1 * 1 := by rw [hxn]; exact mul_le_mul le_rfl hfn (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hAB : 0 ≤ Acoef f x + Bcoef f x := by rw [hApB, hxd]; linarith
  -- disc = (A+B)², so √disc = A+B, t = 1
  have hdisc : discr f x = (Acoef f x + Bcoef f x) ^ 2 := by
    rw [discr]; linear_combination (-Acoef f x) * hkey
  have hsqrt : Real.sqrt (discr f x) = Acoef f x + Bcoef f x := by
    rw [hdisc, Real.sqrt_sq hAB]
  have ht1 : tparam f x = 1 := by
    have hnum : -Bcoef f x + (Acoef f x + Bcoef f x) = Acoef f x := by ring
    rw [tparam, hsqrt, hnum, div_self hA.ne']
  rw [rhoPt, ht1, one_smul, dvec]; abel

/-! ### Continuity of the retraction -/

omit hf in
lemma continuous_fval : Continuous fun x : closedBall (0 : Plane) 1 => (f x : Plane) :=
  continuous_subtype_val.comp (map_continuous f)

omit hf in
lemma continuous_dvec : Continuous (dvec f) :=
  continuous_subtype_val.sub (continuous_fval f)

omit hf in
lemma continuous_Acoef : Continuous (Acoef f) :=
  (continuous_dvec f).inner (continuous_dvec f)

omit hf in
lemma continuous_Bcoef : Continuous (Bcoef f) :=
  (continuous_fval f).inner (continuous_dvec f)

omit hf in
lemma continuous_Ccoef : Continuous (Ccoef f) :=
  ((continuous_fval f).norm.pow 2).sub continuous_const

omit hf in
lemma continuous_discr : Continuous (discr f) :=
  ((continuous_Bcoef f).pow 2).sub ((continuous_Acoef f).mul (continuous_Ccoef f))

lemma continuous_tparam : Continuous (tparam f) :=
  Continuous.div (((continuous_Bcoef f).neg).add (continuous_discr f).sqrt)
    (continuous_Acoef f) (fun x => (Acoef_pos f hf x).ne')

lemma continuous_rhoPt : Continuous (rhoPt f) :=
  (continuous_fval f).add ((continuous_tparam f hf).smul (continuous_dvec f))

end Disk

/-- **Phase 3.** Brouwer's fixed point theorem for the closed unit disk. -/
theorem brouwer_disk (f : C(closedBall (0 : Plane) 1, closedBall (0 : Plane) 1)) :
    ∃ x, f x = x := by
  by_contra hcon
  push Not at hcon
  have hf : ∀ x, (f x : Plane) ≠ (x : Plane) := fun x h => hcon x (Subtype.ext h)
  have hρmem : ∀ x, rhoPt f x ∈ closedBall (0 : Plane) 1 := fun x => by
    rw [mem_closedBall, dist_zero_right, norm_rhoPt f hf x]
  refine no_retraction ⟨fun x => ⟨rhoPt f x, hρmem x⟩, (continuous_rhoPt f hf).subtype_mk _⟩
    (fun x => ?_) (fun x hx => ?_)
  · change rhoPt f x ∈ sphere (0 : Plane) 1
    rw [mem_sphere_zero_iff_norm]; exact norm_rhoPt f hf x
  · change rhoPt f x = (x : Plane)
    exact rhoPt_of_mem_sphere f hf x hx

/-! ## Phase 4 — general nonempty compact convex sets -/

/-- Transfer of the fixed-point property along a homeomorphism. -/
theorem fixedPoint_transfer {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : X ≃ₜ Y) (hY : ∀ g : C(Y, Y), ∃ y, g y = y) (f : C(X, X)) : ∃ x, f x = x := by
  obtain ⟨y, hy⟩ := hY ((⟨φ, φ.continuous⟩ : C(X, Y)).comp
      (f.comp (⟨φ.symm, φ.symm.continuous⟩ : C(Y, X))))
  refine ⟨φ.symm y, ?_⟩
  have hfy : φ (f (φ.symm y)) = y := hy
  calc f (φ.symm y) = φ.symm (φ (f (φ.symm y))) := (φ.symm_apply_apply _).symm
    _ = φ.symm y := by rw [hfy]

/-! ### Brouwer on an arbitrary closed ball (by rescaling) -/

/-- Rescaling homeomorphism `closedBall 0 R ≃ₜ closedBall 0 1` (`x ↦ R⁻¹ • x`). -/
noncomputable def ballScale (R : ℝ) (hR : 0 < R) :
    closedBall (0 : Plane) R ≃ₜ closedBall (0 : Plane) 1 where
  toFun x := ⟨R⁻¹ • (x : Plane), by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
    have hx : ‖(x : Plane)‖ ≤ R := by have := x.2; rwa [mem_closedBall, dist_zero_right] at this
    rw [inv_mul_le_iff₀ hR]; simpa using hx⟩
  invFun y := ⟨R • (y : Plane), by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    have hy : ‖(y : Plane)‖ ≤ 1 := by have := y.2; rwa [mem_closedBall, dist_zero_right] at this
    nlinarith [norm_nonneg (y : Plane)]⟩
  left_inv x := by ext; simp [smul_smul, mul_inv_cancel₀ hR.ne']
  right_inv y := by ext; simp [smul_smul, inv_mul_cancel₀ hR.ne']
  -- `fun_prop` rather than term-mode `Continuous.subtype_mk`: since Mathlib
  -- `905b9581`, unifying `Continuous.subtype_mk _ ?hp` against the `continuous_invFun`
  -- field of this `where` block diverges (it exhausts even a 1M heartbeat budget in
  -- `isDefEq`). Not a proof-size problem — hoisting the membership obligations into
  -- standalone lemmas does not help; only avoiding that unification does.
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- **Brouwer for a closed ball of arbitrary positive radius.** -/
theorem brouwer_ball (R : ℝ) (hR : 0 < R)
    (f : C(closedBall (0 : Plane) R, closedBall (0 : Plane) R)) : ∃ x, f x = x :=
  fixedPoint_transfer (ballScale R hR) (fun g => brouwer_disk g) f

/-! ### Nearest-point projection onto a nonempty compact convex set

Any nonempty compact convex set `s ⊆ ℝ²` is a retract of any closed ball
containing it, via the (nonexpansive, hence continuous) nearest-point
projection.  This yields Brouwer for all such `s` uniformly — in particular the
degenerate empty-interior case is handled without any dimension reduction. -/

section Projection

variable {s : Set Plane} (hconv : Convex ℝ s) (hcomp : IsCompact s) (hne : s.Nonempty)

/-- Nearest-point projection of `u` onto the nonempty compact convex set `s`. -/
noncomputable def projFun (u : Plane) : Plane :=
  (exists_norm_eq_iInf_of_complete_convex hne hcomp.isComplete hconv u).choose

lemma projFun_mem (u : Plane) : projFun hconv hcomp hne u ∈ s :=
  (exists_norm_eq_iInf_of_complete_convex hne hcomp.isComplete hconv u).choose_spec.1

/-- The variational characterization of the projection. -/
lemma projFun_inner_le (u : Plane) {w : Plane} (hw : w ∈ s) :
    ⟪u - projFun hconv hcomp hne u, w - projFun hconv hcomp hne u⟫ ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero hconv (projFun_mem hconv hcomp hne u)).mp
    (exists_norm_eq_iInf_of_complete_convex hne hcomp.isComplete hconv u).choose_spec.2 w hw

/-- The projection fixes the points of `s`. -/
lemma projFun_eq_self {u : Plane} (hu : u ∈ s) : projFun hconv hcomp hne u = u := by
  have h := projFun_inner_le hconv hcomp hne u hu
  rw [real_inner_self_eq_norm_sq] at h
  have hz : u - projFun hconv hcomp hne u = 0 := by
    have hn := norm_nonneg (u - projFun hconv hcomp hne u)
    have : ‖u - projFun hconv hcomp hne u‖ = 0 := by nlinarith
    rwa [norm_eq_zero] at this
  rw [sub_eq_zero] at hz; exact hz.symm

/-- The projection is nonexpansive. -/
lemma projFun_dist_le (u₁ u₂ : Plane) :
    ‖projFun hconv hcomp hne u₁ - projFun hconv hcomp hne u₂‖ ≤ ‖u₁ - u₂‖ := by
  set v₁ := projFun hconv hcomp hne u₁
  set v₂ := projFun hconv hcomp hne u₂
  have hb1 : 0 ≤ ⟪u₁ - v₁, v₁ - v₂⟫ := by
    have h := projFun_inner_le hconv hcomp hne u₁ (projFun_mem hconv hcomp hne u₂)
    rw [show v₂ - v₁ = -(v₁ - v₂) by abel, inner_neg_right] at h
    linarith
  have hb2 : ⟪u₂ - v₂, v₁ - v₂⟫ ≤ 0 :=
    projFun_inner_le hconv hcomp hne u₂ (projFun_mem hconv hcomp hne u₁)
  have decomp : ⟪u₁ - u₂, v₁ - v₂⟫
      = ⟪u₁ - v₁, v₁ - v₂⟫ - ⟪u₂ - v₂, v₁ - v₂⟫ + ⟪v₁ - v₂, v₁ - v₂⟫ := by
    have hsum : u₁ - u₂ = (u₁ - v₁ - (u₂ - v₂)) + (v₁ - v₂) := by abel
    rw [← inner_sub_left, ← inner_add_left, ← hsum]
  have key : ‖v₁ - v₂‖ ^ 2 ≤ ⟪u₁ - u₂, v₁ - v₂⟫ := by
    rw [decomp, ← real_inner_self_eq_norm_sq]; linarith
  have hcs : ⟪u₁ - u₂, v₁ - v₂⟫ ≤ ‖u₁ - u₂‖ * ‖v₁ - v₂‖ := real_inner_le_norm _ _
  rcases (norm_nonneg (v₁ - v₂)).eq_or_lt with h0 | hpos
  · rw [← h0]; exact norm_nonneg _
  · have hsq : ‖v₁ - v₂‖ * ‖v₁ - v₂‖ ≤ ‖u₁ - u₂‖ * ‖v₁ - v₂‖ := by
      rw [← pow_two]; exact le_trans key hcs
    exact le_of_mul_le_mul_right hsq hpos

lemma continuous_projFun : Continuous (projFun hconv hcomp hne) :=
  (LipschitzWith.mk_one (fun u₁ u₂ => by
    rw [dist_eq_norm, dist_eq_norm]; exact projFun_dist_le hconv hcomp hne u₁ u₂)).continuous

end Projection

/-- **The 2D Brouwer fixed point theorem.** Every continuous self-map of a
nonempty compact convex subset of `ℝ²` has a fixed point.  This matches the
`JordanCurve.BrouwerFPT` interface used to discharge the Jordan curve theorem.

The set `s` is contained in a closed ball `closedBall 0 R`; the nearest-point
projection `r : closedBall 0 R → s` is a continuous retraction, so the self-map
`incl ∘ f ∘ r` of the ball has (by `brouwer_ball`) a fixed point `x`, whose
coordinates lie in `s`, whence `r x` is a fixed point of `f`. -/
theorem brouwerFPT : ∀ s : Set Plane, Convex ℝ s → IsCompact s → s.Nonempty →
    ∀ f : C(s, s), ∃ x, f x = x := by
  intro s hconv hcomp hne f
  obtain ⟨R, hR, hsub⟩ := hcomp.isBounded.subset_closedBall_lt 0 0
  let incl : C(s, closedBall (0 : Plane) R) :=
    ⟨fun y => ⟨(y : Plane), hsub y.2⟩, continuous_subtype_val.subtype_mk _⟩
  let r : C(closedBall (0 : Plane) R, s) :=
    ⟨fun x => ⟨projFun hconv hcomp hne (x : Plane), projFun_mem hconv hcomp hne (x : Plane)⟩,
      ((continuous_projFun hconv hcomp hne).comp continuous_subtype_val).subtype_mk _⟩
  obtain ⟨x, hx⟩ := brouwer_ball R hR (incl.comp (f.comp r))
  refine ⟨r x, ?_⟩
  apply Subtype.ext
  have hval : (f (r x) : Plane) = (x : Plane) := congrArg Subtype.val hx
  have hxs : (x : Plane) ∈ s := by rw [← hval]; exact (f (r x)).2
  have hrx : ((r x : s) : Plane) = (x : Plane) := projFun_eq_self hconv hcomp hne hxs
  change (f (r x) : Plane) = ((r x : s) : Plane)
  rw [hval, hrx]

end Brouwer

end JordanCurve
