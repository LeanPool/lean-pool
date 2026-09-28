/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.ForMathlib.Analysis.Foundations.Development001

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Topology.Instances.Matrix
/-!
# Moving sofa: related mathematical developments

* `Geometry.Plane`.
* `Geometry.Basic`.
* `Geometry.Frame`.
* `Geometry.NormalLines`.
* `Geometry.QuadrantBounds`.
* `Geometry.Subgraph`.
* `Geometry.Support`.
* `Geometry.Contacts`.
* `Geometry.FrameCalculus`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Plane
-/

@[expose] public section

namespace MovingSofa

/-- The two-dimensional real Euclidean space used for sofa geometry. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The squared norm of a planar point in coordinates. -/
theorem Point.norm_sq_eq (z : Point) : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

/-- Cauchy-Schwarz for the coordinate form of the planar inner product. -/
theorem Point.abs_inner_coords_le (w d : Point) :
    |w 0 * d 0 + w 1 * d 1| ≤ ‖w‖ * ‖d‖ := by
  have hinner : (inner ℝ w d : ℝ) = w 0 * d 0 + w 1 * d 1 := by
    simp [inner, Fin.sum_univ_two]
    ring
  rw [← hinner]
  exact abs_real_inner_le_norm w d

/-- Each coordinate of a planar point is bounded by its norm. -/
theorem Point.abs_apply_le_norm (z : Point) (i : Fin 2) : |z i| ≤ ‖z‖ := by
  simpa [PiLp.norm_single, EuclideanSpace.inner_single_right] using
    abs_real_inner_le_norm z (EuclideanSpace.single i (1 : ℝ))

end MovingSofa

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Basic
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The normal and positively oriented tangent at an angular direction. -/
def frame (t : Real.Angle) : Point × Point :=
  (!₂[t.cos, t.sin], !₂[-t.sin, t.cos])

/-- The unit normal of the angular frame. -/
abbrev normalVector (t : Real.Angle) : Point := (frame t).1

/-- The counterclockwise unit tangent of the angular frame. -/
abbrev tangentVector (t : Real.Angle) : Point := (frame t).2

/-- The support value; geometric results require a nonempty compact set. -/
def supportValue (s : Set Point) (t : Real.Angle) : ℝ :=
  sSup ((fun p ↦ inner ℝ p (normalVector t)) '' s)

/-- The line with the given unit normal and signed offset. -/
def normalLine (t : Real.Angle) (h : ℝ) : Set Point :=
  {p | inner ℝ p (normalVector t) = h}

/-- A normal half-plane: `upper` chooses the greater side, `strict` its open version. -/
def normalHalfPlane (t : Real.Angle) (h : ℝ) (upper strict : Bool) : Set Point :=
  {p | if upper then
    if strict then h < inner ℝ p (normalVector t) else h ≤ inner ℝ p (normalVector t)
  else
    if strict then inner ℝ p (normalVector t) < h else inner ℝ p (normalVector t) ≤ h}

/-- Closed normal half-planes are closed, on either side of the boundary line. -/
theorem isClosed_normalHalfPlane (t : Real.Angle) (h : ℝ) (upper : Bool) :
    IsClosed (normalHalfPlane t h upper false) := by
  cases upper
  · exact isClosed_le (continuous_id.inner continuous_const) continuous_const
  · exact isClosed_le continuous_const (continuous_id.inner continuous_const)

/-- Closed normal half-planes are convex, on either side of the boundary line. -/
theorem convex_normalHalfPlane (t : Real.Angle) (h : ℝ) (upper : Bool) :
    Convex ℝ (normalHalfPlane t h upper false) := by
  have hlin : IsLinearMap ℝ fun p : Point ↦ inner ℝ p (normalVector t) :=
    isLinearMap_inner_left _
  cases upper
  · exact convex_halfSpace_le hlin h
  · exact convex_halfSpace_ge hlin h

/-- Open normal half-planes are convex, on either side of the boundary line. -/
theorem convex_normalHalfPlane_open (t : Real.Angle) (h : ℝ) (upper : Bool) :
    Convex ℝ (normalHalfPlane t h upper true) := by
  have hlin : IsLinearMap ℝ fun p : Point ↦ inner ℝ p (normalVector t) :=
    isLinearMap_inner_left _
  cases upper
  · exact convex_halfSpace_lt hlin h
  · exact convex_halfSpace_gt hlin h

/-- The supporting line and closed containing half-plane of a nonempty compact set. -/
def supportingLineHalfPlane (s : Set Point) (t : Real.Angle) : Set Point × Set Point :=
  (normalLine t (supportValue s t), normalHalfPlane t (supportValue s t) false false)

/-- A closed supporting half-plane, read through the opposite normal direction. -/
theorem supportingLineHalfPlane_snd_eq_normalHalfPlane {s : Set Point} {t u : Real.Angle}
    {h : ℝ} (hn : normalVector u = -normalVector t) (hs : supportValue s u = -h) :
    (supportingLineHalfPlane s u).2 = normalHalfPlane t h true false := by
  ext q
  change inner ℝ q (normalVector u) ≤ supportValue s u ↔ h ≤ inner ℝ q (normalVector t)
  rw [hn, inner_neg_right, hs]
  constructor <;> intro hq <;> linarith

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Frame
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- Every unit vector is the normal vector of an angular frame. -/
theorem exists_angle_normalVector_eq {u : Point} (hu : ‖u‖ = 1) :
    ∃ t : Real.Angle, normalVector t = u := by
  let z : ℂ := ⟨u 0, u 1⟩
  have hzNorm : ‖z‖ = 1 := by
    rw [Complex.norm_def, show Complex.normSq z = ‖u‖ ^ 2 by
      rw [EuclideanSpace.norm_sq_eq]
      simp [z, Complex.normSq_apply, Fin.sum_univ_two, pow_two, Real.norm_eq_abs]]
    simp [hu]
  have hz : z ≠ 0 := by
    intro hz
    simp [hz] at hzNorm
  refine ⟨(z.arg : ℝ), ?_⟩
  ext i
  fin_cases i
  · simpa [normalVector, frame, z, hzNorm] using Complex.cos_arg hz
  · simpa [normalVector, frame, z, hzNorm] using Complex.sin_arg z

theorem continuous_normalVector_real :
    Continuous (fun t : ℝ ↦ normalVector (t : Real.Angle)) := by
  let c : ℝ → (i : Fin 2) → ℝ := fun t i ↦
    Fin.cases (Real.cos t) (fun _ ↦ Real.sin t) i
  have hc : Continuous c := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact Real.continuous_cos
    · exact Real.continuous_sin
  have heq : (fun t : ℝ ↦ normalVector (t : Real.Angle)) =
      (fun t ↦ WithLp.toLp 2 (c t)) := by
    funext t
    ext i
    fin_cases i <;> rfl
  rw [heq]
  exact (PiLp.continuous_toLp (2 : ENNReal) (fun _ : Fin 2 ↦ ℝ)).comp hc

/-- Opposite real angles give opposite normal vectors. -/
theorem normalVector_add_pi (t : ℝ) :
    normalVector ((t + Real.pi : ℝ) : Real.Angle) = -normalVector (t : Real.Angle) := by
  ext i
  fin_cases i <;> simp [normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe]

/-- Opposite real angles give opposite tangent vectors. -/
theorem tangentVector_add_pi (t : ℝ) :
    tangentVector ((t + Real.pi : ℝ) : Real.Angle) = -tangentVector (t : Real.Angle) := by
  ext i
  fin_cases i <;> simp [tangentVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe]

/-- The projection onto the normal direction of a real angle, in coordinates. -/
theorem inner_normalVector_real (p : Point) (t : ℝ) :
    inner ℝ p (normalVector (t : Real.Angle)) = p 0 * Real.cos t + p 1 * Real.sin t := by
  simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- The projection onto the tangent direction of a real angle, in coordinates. -/
theorem inner_tangentVector_real (p : Point) (t : ℝ) :
    inner ℝ p (tangentVector (t : Real.Angle)) = -(p 0 * Real.sin t) + p 1 * Real.cos t := by
  simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- The inner product of two unit normals is the cosine of their angle difference. -/
theorem inner_normalVector_normalVector (s t : ℝ) :
    inner ℝ (normalVector (s : Real.Angle)) (normalVector (t : Real.Angle)) =
      Real.cos (s - t) := by
  simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, Real.cos_sub]
  ring

/-- A normal vector has squared length one. -/
theorem inner_normalVector_self (t : ℝ) :
    inner ℝ (normalVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = 1 := by
  rw [inner_normalVector_normalVector]
  simp

/-- A normal vector at an angle has squared length one. -/
theorem inner_normalVector_self_angle (t : Real.Angle) :
    inner ℝ (normalVector t) (normalVector t) = 1 := by
  induction t using Real.Angle.induction_on with
  | _ r => exact inner_normalVector_self r

/-- A normal vector at a real angle has length one. -/
theorem norm_normalVector_real (t : ℝ) : ‖normalVector (t : Real.Angle)‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [EuclideanSpace.norm_sq_eq]
  simp [normalVector, frame, Fin.sum_univ_two]

theorem inner_normalVector_smul_add_inner_tangentVector_smul (p : Point) (t : Real.Angle) :
    inner ℝ p (normalVector t) • normalVector t +
      inner ℝ p (tangentVector t) • tangentVector t = p := by
  ext i
  fin_cases i <;>
    simp [normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two] <;>
    nlinarith [congrArg (fun r : ℝ ↦ r * p 0) t.cos_sq_add_sin_sq,
      congrArg (fun r : ℝ ↦ r * p 1) t.cos_sq_add_sin_sq]

theorem normalVector_add_real (t δ : ℝ) :
    normalVector ((t + δ : ℝ) : Real.Angle) =
      Real.cos δ • normalVector (t : Real.Angle) +
      Real.sin δ • tangentVector (t : Real.Angle) := by
  ext i
  fin_cases i <;> simp [normalVector, tangentVector, frame, -Real.Angle.coe_add, Real.cos_add,
    Real.sin_add] <;> ring

theorem inner_normalVector_tangentVector (t : ℝ) :
    inner ℝ (normalVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = 0 := by
  simp [normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem inner_tangentVector_self (t : ℝ) :
    inner ℝ (tangentVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = 1 := by
  rw [PiLp.inner_apply]
  simp [tangentVector, frame, Fin.sum_univ_two, Real.sin_sq_add_cos_sq]

theorem tangentVector_add_pi_div_two (t : ℝ) :
    tangentVector ((t + Real.pi / 2 : ℝ) : Real.Angle) = -normalVector (t : Real.Angle) := by
  ext i
  fin_cases i <;> simp [normalVector, tangentVector, frame,
    Real.Angle.sin_add_pi_div_two, Real.Angle.cos_add_pi_div_two]

/-- Adding pi to an angle reverses its normal vector. -/
theorem normalVector_add_pi_angle (a : Real.Angle) :
    normalVector (a + ((Real.pi : ℝ) : Real.Angle)) = -normalVector a := by
  induction a using Real.Angle.induction_on with
  | _ a => simpa only [Real.Angle.coe_add] using normalVector_add_pi a

/-- The sine convolution kernel is the negative normal projection of the moving tangent. -/
theorem sin_sub_eq_neg_inner_normalVector_tangentVector (t u : Real.Angle) :
    (u - t).sin = -inner ℝ (normalVector t) (tangentVector u) := by
  induction t using Real.Angle.induction_on with
  | _ t =>
    induction u using Real.Angle.induction_on with
    | _ u =>
      change Real.sin (u - t) = _
      simp [normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
        Real.sin_sub]
      ring

/-- The normal projection of a tangent vector is the sine of the angle difference. -/
theorem inner_tangentVector_normalVector_real (t s : ℝ) :
    inner ℝ (tangentVector (t : Real.Angle)) (normalVector (s : Real.Angle)) =
      Real.sin (s - t) := by
  simp [tangentVector, normalVector, frame, PiLp.inner_apply, Real.sin_sub]
  ring

/-- The inner product of two unit tangents is the cosine of their angle difference. -/
theorem inner_tangentVector_tangentVector (s t : ℝ) :
    inner ℝ (tangentVector (s : Real.Angle)) (tangentVector (t : Real.Angle)) =
      Real.cos (s - t) := by
  simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two, Real.cos_sub]
  ring

/-- The normal coordinate of a vector in the frame at another angle. -/
theorem inner_normalVector_eq_frame_rotate (w : Point) (s t : ℝ) :
    inner ℝ w (normalVector (t : Real.Angle)) =
      inner ℝ w (normalVector (s : Real.Angle)) * Real.cos (s - t) -
        inner ℝ w (tangentVector (s : Real.Angle)) * Real.sin (s - t) := by
  nth_rewrite 1 [← inner_normalVector_smul_add_inner_tangentVector_smul w (s : Real.Angle)]
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_normalVector_normalVector, inner_tangentVector_normalVector_real,
    show t - s = -(s - t) by ring, Real.sin_neg]
  ring

/-- The tangent coordinate of a vector in the frame at another angle. -/
theorem inner_tangentVector_eq_frame_rotate (w : Point) (s t : ℝ) :
    inner ℝ w (tangentVector (t : Real.Angle)) =
      inner ℝ w (normalVector (s : Real.Angle)) * Real.sin (s - t) +
        inner ℝ w (tangentVector (s : Real.Angle)) * Real.cos (s - t) := by
  have hcross : inner ℝ (normalVector (s : Real.Angle)) (tangentVector (t : Real.Angle)) =
      Real.sin (s - t) := by
    rw [real_inner_comm]
    exact inner_tangentVector_normalVector_real t s
  nth_rewrite 1 [← inner_normalVector_smul_add_inner_tangentVector_smul w (s : Real.Angle)]
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_tangentVector_tangentVector, hcross]

/-- Two points whose normal coordinates agree at two transverse angles coincide. -/
theorem eq_of_inner_normalVector_eq {p q : Point} {s t : ℝ}
    (hst : Real.sin (s - t) ≠ 0)
    (hs : inner ℝ p (normalVector (s : Real.Angle)) =
      inner ℝ q (normalVector (s : Real.Angle)))
    (ht : inner ℝ p (normalVector (t : Real.Angle)) =
      inner ℝ q (normalVector (t : Real.Angle))) : p = q := by
  have hp := inner_normalVector_eq_frame_rotate p s t
  have hq := inner_normalVector_eq_frame_rotate q s t
  have hmul : (inner ℝ p (tangentVector (s : Real.Angle)) -
      inner ℝ q (tangentVector (s : Real.Angle))) * Real.sin (s - t) = 0 := by
    linear_combination hp - hq - ht + Real.cos (s - t) * hs
  have hv : inner ℝ p (tangentVector (s : Real.Angle)) =
      inner ℝ q (tangentVector (s : Real.Angle)) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hst)
  calc p = inner ℝ p (normalVector (s : Real.Angle)) • normalVector (s : Real.Angle) +
        inner ℝ p (tangentVector (s : Real.Angle)) • tangentVector (s : Real.Angle) :=
        (inner_normalVector_smul_add_inner_tangentVector_smul p (s : Real.Angle)).symm
    _ = inner ℝ q (normalVector (s : Real.Angle)) • normalVector (s : Real.Angle) +
        inner ℝ q (tangentVector (s : Real.Angle)) • tangentVector (s : Real.Angle) := by
        rw [hs, hv]
    _ = q := inner_normalVector_smul_add_inner_tangentVector_smul q (s : Real.Angle)

/-- Each coordinate of the frame tangent is continuous in the angle. -/
theorem continuous_tangentVector_coordinate (i : Fin 2) :
    Continuous fun u : Real.Angle ↦ tangentVector u i := by
  fin_cases i
  · exact Real.Angle.continuous_sin.neg
  · exact Real.Angle.continuous_cos

/-- The frame tangent is a unit vector. -/
theorem norm_tangentVector (t : Real.Angle) : ‖tangentVector t‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1), Point.norm_sq_eq]
  simp [tangentVector, frame, add_comm]

/-- Each coordinate of the frame tangent is bounded by one. -/
theorem norm_tangentVector_coordinate_le_one (t : Real.Angle) (i : Fin 2) :
    ‖tangentVector t i‖ ≤ 1 := by
  simpa [Real.norm_eq_abs, norm_tangentVector t] using
    Point.abs_apply_le_norm (tangentVector t) i

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Normal Lines
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- A nontrivial segment has at most one normal direction strictly between zero and pi. -/
theorem eq_of_inner_sub_normalVector_eq_zero_of_ne {a b : Point} {s t : ℝ}
    (hs : s ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi) (hab : a ≠ b)
    (horths : inner ℝ (b - a) (normalVector (s : Real.Angle)) = 0)
    (hortht : inner ℝ (b - a) (normalVector (t : Real.Angle)) = 0) : s = t := by
  have hs' : (b 0 - a 0) * Real.cos s + (b 1 - a 1) * Real.sin s = 0 := by
    simpa [normalVector, frame, PiLp.inner_apply, mul_comm] using horths
  have ht' : (b 0 - a 0) * Real.cos t + (b 1 - a 1) * Real.sin t = 0 := by
    simpa [normalVector, frame, PiLp.inner_apply, mul_comm] using hortht
  have hxprod : (b 0 - a 0) * Real.sin (s - t) = 0 := by
    rw [Real.sin_sub]
    linear_combination Real.sin s * ht' - Real.sin t * hs'
  have hyprod : (b 1 - a 1) * Real.sin (s - t) = 0 := by
    rw [Real.sin_sub]
    linear_combination Real.cos t * hs' - Real.cos s * ht'
  have hsin : Real.sin (s - t) = 0 := by
    by_contra hne
    have hx : b 0 = a 0 := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp hxprod).resolve_right hne)
    have hy : b 1 = a 1 := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp hyprod).resolve_right hne)
    apply hab
    ext i
    fin_cases i
    · exact hx.symm
    · exact hy.symm
  have hz := (Real.sin_eq_zero_iff_of_lt_of_lt
    (by linarith [hs.1, ht.2]) (by linarith [hs.2, ht.1])).mp hsin
  linarith

/-- Normal lines with angles strictly between zero and pi agree exactly when their data agree. -/
theorem normalLine_eq_iff_of_mem_Ioo {s t c d : ℝ}
    (hs : s ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi) :
    normalLine (s : Real.Angle) c = normalLine (t : Real.Angle) d ↔
      s = t ∧ c = d := by
  constructor
  · intro hline
    let p := c • normalVector (s : Real.Angle)
    let q := p + tangentVector (s : Real.Angle)
    have hp : p ∈ normalLine (s : Real.Angle) c := by
      change inner ℝ p (normalVector (s : Real.Angle)) = c
      rw [show p = c • normalVector (s : Real.Angle) by rfl,
        real_inner_smul_left, inner_normalVector_self]
      simp
    have hq : q ∈ normalLine (s : Real.Angle) c := by
      change inner ℝ q (normalVector (s : Real.Angle)) = c
      rw [show q = p + tangentVector (s : Real.Angle) by rfl, inner_add_left]
      rw [show inner ℝ p (normalVector (s : Real.Angle)) = c by exact hp]
      rw [real_inner_comm, inner_normalVector_tangentVector, add_zero]
    have hp' : p ∈ normalLine (t : Real.Angle) d := hline ▸ hp
    have hq' : q ∈ normalLine (t : Real.Angle) d := hline ▸ hq
    have hv : tangentVector (s : Real.Angle) ≠ 0 := by
      intro hz
      have hinner := inner_tangentVector_self s
      rw [hz, inner_zero_left] at hinner
      norm_num at hinner
    have hsorth : inner ℝ (tangentVector (s : Real.Angle))
        (normalVector (s : Real.Angle)) = 0 := by
      rw [real_inner_comm, inner_normalVector_tangentVector]
    have htorth : inner ℝ (tangentVector (s : Real.Angle))
        (normalVector (t : Real.Angle)) = 0 := by
      rw [show tangentVector (s : Real.Angle) = q - p by simp [q]]
      rw [inner_sub_left, show inner ℝ q (normalVector (t : Real.Angle)) = d by exact hq',
        show inner ℝ p (normalVector (t : Real.Angle)) = d by exact hp', sub_self]
    have hst := eq_of_inner_sub_normalVector_eq_zero_of_ne
      (a := 0) (b := tangentVector (s : Real.Angle)) hs ht hv.symm
      (by simpa using hsorth) (by simpa using htorth)
    subst t
    refine ⟨rfl, ?_⟩
    change inner ℝ p (normalVector (s : Real.Angle)) = d at hp'
    rw [show inner ℝ p (normalVector (s : Real.Angle)) = c by exact hp] at hp'
    exact hp'
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Opposite normal angles describe the same line with the opposite offset. -/
theorem normalLine_eq_of_cut {a b c : ℝ}
    (hab : ((b : ℝ) : Real.Angle) = ((a + Real.pi : ℝ) : Real.Angle)) :
    normalLine ((b : ℝ) : Real.Angle) c = normalLine ((a : ℝ) : Real.Angle) (-c) := by
  rw [hab]
  ext p
  simp only [normalLine, Set.mem_ofPred_eq, normalVector_add_pi, inner_neg_right]
  constructor <;> intro h <;> linarith only [h]
end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Quadrant Bounds
-/

@[expose] public section

namespace MovingSofa

/-- A horizontal lower bound cuts a first-quadrant pair of upper projection bounds to a bounded set.
-/
theorem isBounded_setOf_le_snd_and_inner_lt (a b c t : ℝ) (ht : t ∈ Set.Ioo 0 (Real.pi / 2)) :
    Bornology.IsBounded {p : Point | a ≤ p 1 ∧
      inner ℝ p (normalVector (t : Real.Angle)) < b ∧
      inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) < c} := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (ht.2.trans (by linarith [Real.pi_pos]))
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  apply (EuclideanSpace.isBounded_coordinate_rectangle ((Real.cos t * a - c) / Real.sin t)
    ((b - Real.sin t * a) / Real.cos t) a (Real.sin t * b + Real.cos t * c)).subset
  rintro p ⟨hy, h₁, h₂⟩
  have hb : Real.cos t * p 0 + Real.sin t * p 1 < b := by
    simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, mul_comm] using h₁
  have hd : -Real.sin t * p 0 + Real.cos t * p 1 < c := by
    simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
      Real.cos_add, Real.sin_add, -Real.Angle.coe_add, mul_comm] using h₂
  refine ⟨?_, ?_, hy, ?_⟩
  · apply (div_le_iff₀ hs).2
    nlinarith only [hd, mul_le_mul_of_nonneg_left hy hc.le]
  · apply (le_div_iff₀ hc).2
    nlinarith only [hb, mul_le_mul_of_nonneg_left hy hs.le]
  · have hyid : (Real.sin t ^ 2 + Real.cos t ^ 2) * p 1 = p 1 := by
      rw [Real.sin_sq_add_cos_sq, one_mul]
    have hb' := mul_lt_mul_of_pos_left hb hs
    have hd' := mul_lt_mul_of_pos_left hd hc
    nlinarith only [hyid, hb', hd']

end MovingSofa

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# The planar region under the graph of a function

For `a b : ℝ` and `f : ℝ → ℝ` this file describes the three planar regions between the
horizontal axis and the graph of `f` over `[a, b]`: `closedSubgraph`, which contains both the
base segment and the graph, `strictSubgraph`, which contains the base but not the graph, and
`openSubgraph`, which contains neither.

For a function continuous on `[a, b]`, vanishing at `a` and `b` and positive in between, the
closed region is the closure of either smaller region (`closure_openSubgraph`,
`closure_strictSubgraph`) and the open region is its interior (`interior_closedSubgraph`).
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- A planar point is recovered from its two coordinates. -/
theorem Point.eq_vecNotation (z : Point) : z = !₂[z 0, z 1] := by
  ext i
  fin_cases i <;> simp

/-- The closed region between the base and the graph of `f` over `[a, b]`. -/
def closedSubgraph (a b : ℝ) (f : ℝ → ℝ) : Set Point :=
  {q | a ≤ q 0 ∧ q 0 ≤ b ∧ 0 ≤ q 1 ∧ q 1 ≤ f (q 0)}

/-- The region under the graph of `f` over `[a, b]`, including the base but not the graph. -/
def strictSubgraph (a b : ℝ) (f : ℝ → ℝ) : Set Point :=
  {q | a ≤ q 0 ∧ q 0 ≤ b ∧ 0 ≤ q 1 ∧ q 1 < f (q 0)}

/-- The open region strictly between the base and the graph of `f` over `(a, b)`. -/
def openSubgraph (a b : ℝ) (f : ℝ → ℝ) : Set Point :=
  {q | a < q 0 ∧ q 0 < b ∧ 0 < q 1 ∧ q 1 < f (q 0)}

section Subgraph

variable {a b : ℝ} {f : ℝ → ℝ}

/-- The open subgraph omits the base, which the strict subgraph contains. -/
theorem openSubgraph_subset_strictSubgraph : openSubgraph a b f ⊆ strictSubgraph a b f :=
  fun _ h ↦ ⟨h.1.le, h.2.1.le, h.2.2.1.le, h.2.2.2⟩

/-- The strict subgraph omits the graph, which the closed subgraph contains. -/
theorem strictSubgraph_subset_closedSubgraph : strictSubgraph a b f ⊆ closedSubgraph a b f :=
  fun _ h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.le⟩

/-- The open subgraph is contained in the closed one. -/
theorem openSubgraph_subset_closedSubgraph : openSubgraph a b f ⊆ closedSubgraph a b f :=
  openSubgraph_subset_strictSubgraph.trans strictSubgraph_subset_closedSubgraph

/-- The vertical line through a fixed horizontal coordinate is continuous. -/
private theorem continuous_verticalLine (c : ℝ) :
    Continuous fun y : ℝ ↦ (!₂[c, y] : Point) :=
  (PiLp.continuous_toLp (2 : ENNReal) fun _ : Fin 2 ↦ ℝ).comp
    (continuous_const.matrixVecCons (continuous_id.matrixVecCons continuous_const))

/-- The closed subgraph of a function continuous on the base interval is closed. -/
theorem isClosed_closedSubgraph (hf : ContinuousOn f (Set.Icc a b)) :
    IsClosed (closedSubgraph a b f) := by
  have hc0 : Continuous fun q : Point ↦ q 0 := PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0
  have hc1 : Continuous fun q : Point ↦ q 1 := PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1
  have hSclosed : IsClosed {q : Point | q 0 ∈ Set.Icc a b} := isClosed_Icc.preimage hc0
  have hgS : ContinuousOn (fun q : Point ↦ f (q 0) - q 1) {q : Point | q 0 ∈ Set.Icc a b} :=
    (hf.comp hc0.continuousOn fun q hq ↦ hq).sub hc1.continuousOn
  have hone := hgS.preimage_isClosed_of_isClosed hSclosed (isClosed_Ici (a := (0 : ℝ)))
  have htwo : IsClosed {q : Point | 0 ≤ q 1} := isClosed_Ici.preimage hc1
  have hsplit : closedSubgraph a b f = ({q : Point | q 0 ∈ Set.Icc a b} ∩
      (fun q : Point ↦ f (q 0) - q 1) ⁻¹' Set.Ici 0) ∩ {q : Point | 0 ≤ q 1} := by
    ext q
    simp only [closedSubgraph, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Icc,
      Set.mem_preimage, Set.mem_Ici, sub_nonneg]
    tauto
  rw [hsplit]
  exact hone.inter htwo

/-- The open subgraph of a function continuous on the base interval is open. -/
theorem isOpen_openSubgraph (hf : ContinuousOn f (Set.Icc a b)) :
    IsOpen (openSubgraph a b f) := by
  have hc0 : Continuous fun q : Point ↦ q 0 := PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0
  have hc1 : Continuous fun q : Point ↦ q 1 := PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1
  rw [isOpen_iff_mem_nhds]
  rintro p ⟨h1, h2, h3, h4⟩
  have hfat : ContinuousAt f (p 0) :=
    (hf.mono Set.Ioo_subset_Icc_self).continuousAt (Ioo_mem_nhds h1 h2)
  have hgap : ContinuousAt (fun q : Point ↦ f (q 0) - q 1) p :=
    (ContinuousAt.comp (g := f) (f := fun q : Point ↦ q 0) (x := p) hfat
      hc0.continuousAt).sub hc1.continuousAt
  filter_upwards [hc0.continuousAt (isOpen_Ioo.mem_nhds (⟨h1, h2⟩ : p 0 ∈ Set.Ioo a b)),
    hc1.continuousAt (isOpen_Ioi.mem_nhds (show p 1 ∈ Set.Ioi (0 : ℝ) from h3)),
    hgap (isOpen_Ioi.mem_nhds (show f (p 0) - p 1 ∈ Set.Ioi (0 : ℝ) from sub_pos.mpr h4))]
    with q hq1 hq2 hq3
  exact ⟨hq1.1, hq1.2, hq2, by simpa using sub_pos.mp hq3⟩

/-- The closed subgraph is the closure of the open one: interior graph points are limits from
below, base points at interior horizontal coordinates are limits from above, and the two
corners are limits of half-height points over the open base interval. -/
theorem closure_openSubgraph (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    (ha : f a = 0) (hb : f b = 0) (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x) :
    closure (openSubgraph a b f) = closedSubgraph a b f := by
  refine Set.Subset.antisymm ((isClosed_closedSubgraph hf).closure_subset_iff.mpr ?_) ?_
  · rintro q ⟨h1, h2, h3, h4⟩
    exact ⟨h1.le, h2.le, h3.le, h4.le⟩
  · have hF : ContinuousOn (fun c ↦ (!₂[c, f c / 2] : Point)) (Set.Icc a b) :=
      (PiLp.continuous_toLp (2 : ENNReal) fun _ : Fin 2 ↦ ℝ).comp_continuousOn
        (continuous_id.continuousOn.matrixVecCons
          ((hf.div_const 2).matrixVecCons continuousOn_const))
    have hFsub : (fun c ↦ (!₂[c, f c / 2] : Point)) '' Set.Ioo a b ⊆ openSubgraph a b f := by
      rintro _ ⟨c, hc, rfl⟩
      have hfc := hpos c hc
      exact ⟨by simpa using hc.1, by simpa using hc.2, by simpa using by linarith,
        by simpa using by linarith⟩
    have hcl : closure (Set.Ioo a b) = Set.Icc a b := closure_Ioo hab.ne
    have hF' : ContinuousOn (fun c ↦ (!₂[c, f c / 2] : Point)) (closure (Set.Ioo a b)) := by
      rw [hcl]; exact hF
    have hcorner : ∀ c ∈ Set.Icc a b, (!₂[c, f c / 2] : Point) ∈ closure (openSubgraph a b f) :=
      fun c hc ↦ closure_mono hFsub (hF'.image_closure ⟨c, by rw [hcl]; exact hc, rfl⟩)
    rintro q ⟨h1, h2, h3, h4⟩
    rcases eq_or_lt_of_le h1 with hqa | hqa
    · have : q 1 = 0 := le_antisymm (by rw [← hqa, ha] at h4; exact h4) h3
      have hq : q = !₂[a, f a / 2] := by
        rw [Point.eq_vecNotation q, ← hqa, this, ha]
        norm_num
      rw [hq]
      exact hcorner a ⟨le_rfl, hab.le⟩
    rcases eq_or_lt_of_le h2 with hqb | hqb
    · have : q 1 = 0 := le_antisymm (by rw [hqb, hb] at h4; exact h4) h3
      have hq : q = !₂[b, f b / 2] := by
        rw [Point.eq_vecNotation q, hqb, this, hb]
        norm_num
      rw [hq]
      exact hcorner b ⟨hab.le, le_rfl⟩
    · have hfc : 0 < f (q 0) := hpos _ ⟨hqa, hqb⟩
      have hsub : (fun y : ℝ ↦ (!₂[q 0, y] : Point)) '' Set.Ioo 0 (f (q 0)) ⊆
          openSubgraph a b f := by
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨by simpa using hqa, by simpa using hqb, by simpa using hy.1,
          by simpa using hy.2⟩
      refine closure_mono hsub ?_
      have := image_closure_subset_closure_image (continuous_verticalLine (q 0))
        (s := Set.Ioo 0 (f (q 0)))
        ⟨q 1, by rw [closure_Ioo hfc.ne]; exact ⟨h3, h4⟩, rfl⟩
      have heq : (!₂[q 0, q 1] : Point) = q := (Point.eq_vecNotation q).symm
      simpa only [heq] using this

/-- A point of the closed subgraph which is not in the open one lies on the base or on the
graph, hence is a limit of points outside the closed subgraph. -/
private theorem mem_closure_compl_closedSubgraph (ha : f a = 0) (hb : f b = 0)
    {q : Point} (hq : q ∈ closedSubgraph a b f)
    (hq' : q ∉ openSubgraph a b f) : q ∈ closure (closedSubgraph a b f)ᶜ := by
  obtain ⟨h1, h2, h3, h4⟩ := hq
  have hbelow : q 1 = 0 → q ∈ closure (closedSubgraph a b f)ᶜ := by
    intro hz
    have hsub : (fun y : ℝ ↦ (!₂[q 0, y] : Point)) '' Set.Iio 0 ⊆
        (closedSubgraph a b f)ᶜ := by
      rintro _ ⟨y, hy, rfl⟩
      intro hmem
      have h := hmem.2.2.1
      simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
      exact absurd h (not_le.mpr hy)
    refine closure_mono hsub ?_
    have := image_closure_subset_closure_image (continuous_verticalLine (q 0)) (s := Set.Iio 0)
      ⟨q 1, by rw [closure_Iio]; exact hz.le, rfl⟩
    have heq : (!₂[q 0, q 1] : Point) = q := (Point.eq_vecNotation q).symm
    simpa only [heq] using this
  rcases eq_or_lt_of_le h3 with hz | hz
  · exact hbelow hz.symm
  rcases eq_or_lt_of_le h4 with htop | htop
  · -- the point sits on the graph, which is strictly above the base here
    have hfpos : 0 < f (q 0) := htop ▸ hz
    have hsub : (fun y : ℝ ↦ (!₂[q 0, y] : Point)) '' Set.Ioi (f (q 0)) ⊆
        (closedSubgraph a b f)ᶜ := by
      rintro _ ⟨y, hy, rfl⟩
      intro hmem
      have h := hmem.2.2.2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
      exact absurd h (not_le.mpr hy)
    refine closure_mono hsub ?_
    have := image_closure_subset_closure_image (continuous_verticalLine (q 0))
      (s := Set.Ioi (f (q 0))) ⟨q 1, by rw [closure_Ioi]; exact htop.ge, rfl⟩
    have heq : (!₂[q 0, q 1] : Point) = q := (Point.eq_vecNotation q).symm
    simpa only [heq] using this
  · -- strictly between base and graph: the horizontal coordinate must be interior
    exfalso
    have hfpos : 0 < f (q 0) := hz.trans htop
    have hqa : a < q 0 := by
      rcases eq_or_lt_of_le h1 with h | h
      · rw [← h, ha] at hfpos; exact absurd hfpos (lt_irrefl 0)
      · exact h
    have hqb : q 0 < b := by
      rcases eq_or_lt_of_le h2 with h | h
      · rw [h, hb] at hfpos; exact absurd hfpos (lt_irrefl 0)
      · exact h
    exact hq' ⟨hqa, hqb, hz, htop⟩

/-- The open subgraph is the interior of the closed one. -/
theorem interior_closedSubgraph (hf : ContinuousOn f (Set.Icc a b))
    (ha : f a = 0) (hb : f b = 0) :
    interior (closedSubgraph a b f) = openSubgraph a b f := by
  refine Set.Subset.antisymm ?_ (interior_maximal openSubgraph_subset_closedSubgraph
    (isOpen_openSubgraph hf))
  intro q hq
  by_contra hqU
  have h2 := mem_closure_compl_closedSubgraph ha hb (interior_subset hq) hqU
  rw [closure_compl] at h2
  exact h2 hq

/-- The closed subgraph is also the closure of the strict subgraph. -/
theorem closure_strictSubgraph (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    (ha : f a = 0) (hb : f b = 0) (hpos : ∀ x ∈ Set.Ioo a b, 0 < f x) :
    closure (strictSubgraph a b f) = closedSubgraph a b f := by
  refine Set.Subset.antisymm
    ((isClosed_closedSubgraph hf).closure_subset_iff.mpr
      strictSubgraph_subset_closedSubgraph) ?_
  rw [← closure_openSubgraph hab hf ha hb hpos]
  exact closure_mono openSubgraph_subset_strictSubgraph

end Subgraph

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Support
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- A compact convex body attains its support value in every normal direction. -/
theorem exists_mem_inner_eq_supportValue (K : ConvexBody Point) (t : Real.Angle) :
    ∃ p ∈ (K : Set Point), inner ℝ p (normalVector t) = supportValue K t := by
  obtain ⟨p, hp, hmax, _⟩ := K.isCompact.exists_sSup_image_eq_and_ge
    (f := fun p : Point ↦ inner ℝ p (normalVector t)) K.nonempty
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
  exact ⟨p, hp, by simpa only [supportValue] using hmax.symm⟩

/-- Translating a nonempty compact set adds the normal component to its support value. -/
theorem supportValue_image_add_of_isCompact {s : Set Point}
    (hs : IsCompact s) (hne : s.Nonempty) (v : Point) (t : Real.Angle) :
    supportValue ((fun p ↦ p + v) '' s) t =
      supportValue s t + inner ℝ v (normalVector t) := by
  obtain ⟨x, hx, hmax, hbound⟩ := hs.exists_sSup_image_eq_and_ge
    (f := fun p : Point ↦ inner ℝ p (normalVector t)) hne
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨x + v, ⟨x, hx, rfl⟩, ?_⟩
    simpa only [inner_add_left, supportValue] using congrArg
      (fun r ↦ r + inner ℝ v (normalVector t)) hmax.symm
  · rintro z ⟨y, ⟨p, hp, rfl⟩, rfl⟩
    simp only [inner_add_left]
    simpa only [supportValue, hmax] using
      add_le_add (hbound p hp) (le_refl (inner ℝ v (normalVector t)))

/-- Translating a compact convex body adds the normal component of the translation to support. -/
theorem supportValue_image_add (K : ConvexBody Point) (v : Point) (t : Real.Angle) :
    supportValue ((fun p ↦ p + v) '' (K : Set Point)) t =
      supportValue K t + inner ℝ v (normalVector t) :=
  supportValue_image_add_of_isCompact K.isCompact K.nonempty v t

/-- Every point of a compact set lies below its support value. -/
theorem inner_le_supportValue_of_isCompact {s : Set Point}
    (hs : IsCompact s) {p : Point} (hp : p ∈ s) (a : Real.Angle) :
    inner ℝ p (normalVector a) ≤ supportValue s a := by
  apply le_csSup (hs.image
    (continuous_inner.comp (continuous_id.prodMk continuous_const))).bddAbove
  exact ⟨p, hp, rfl⟩

/-- A point of a convex body lies below each supporting line. -/
theorem inner_le_supportValue (K : ConvexBody Point) {p : Point}
    (hp : p ∈ K) (t : Real.Angle) : inner ℝ p (normalVector t) ≤ supportValue K t :=
  inner_le_supportValue_of_isCompact K.isCompact hp t

/-- Containment in a closed normal half-plane bounds the support value. -/
theorem supportValue_le_of_subset_normalHalfPlane (K : ConvexBody Point)
    (t : Real.Angle) (c : ℝ)
    (hK : (K : Set Point) ⊆ normalHalfPlane t c false false) :
    supportValue K t ≤ c := by
  apply csSup_le (K.nonempty.image _)
  rintro _ ⟨p, hp, rfl⟩
  exact hK hp

/-- Enlarging a nonempty set without increasing its directional upper bound preserves support. -/
theorem supportValue_eq_of_subset_of_inner_le {s u : Set Point}
    (hs : s.Nonempty) (hsu : s ⊆ u) (a : Real.Angle)
    (hu : ∀ p ∈ u, inner ℝ p (normalVector a) ≤ supportValue s a) :
    supportValue u a = supportValue s a := by
  have hbounded : BddAbove ((fun p ↦ inner ℝ p (normalVector a)) '' u) :=
    ⟨supportValue s a, by rintro _ ⟨p, hp, rfl⟩; exact hu p hp⟩
  apply le_antisymm
  · exact csSup_le ((hs.mono hsu).image _) (by rintro _ ⟨p, hp, rfl⟩; exact hu p hp)
  · exact csSup_le_csSup hbounded (hs.image _) (Set.image_mono hsu)

/-- A convex set meets every intermediate level of a linear functional. -/
theorem exists_mem_inner_eq_of_convex {s : Set Point} (hconv : Convex ℝ s)
    {A C : Point} (hA : A ∈ s) (hC : C ∈ s) {u : Point} {c : ℝ}
    (hCle : inner ℝ C u ≤ c) (hAge : c ≤ inner ℝ A u) :
    ∃ q ∈ s, inner ℝ q u = c := by
  rcases eq_or_lt_of_le (hCle.trans hAge) with heq | hlt
  · exact ⟨C, hC, le_antisymm hCle (heq ▸ hAge)⟩
  · set d : ℝ := inner ℝ A u - inner ℝ C u with hd
    have hdpos : 0 < d := by simp only [hd]; linarith
    set lam : ℝ := (c - inner ℝ C u) / d with hlam
    have hlam0 : 0 ≤ lam := div_nonneg (by linarith) hdpos.le
    have hlam1 : lam ≤ 1 := by
      rw [hlam, div_le_one hdpos]
      simp only [hd]; linarith
    refine ⟨lam • A + (1 - lam) • C, hconv hA hC hlam0 (by linarith) (by ring), ?_⟩
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hlam]
    field_simp
    simp only [hd]
    ring

/-- Support bound in the direction opposite to a cut line lying below the set. -/
theorem supportValue_le_of_cut {s : Set Point} (hne : s.Nonempty) {a b c : ℝ}
    (hab : ((b : ℝ) : Real.Angle) = ((a + Real.pi : ℝ) : Real.Angle))
    (hs : ∀ p ∈ s, c ≤ inner ℝ p (normalVector (a : Real.Angle))) :
    supportValue s ((b : ℝ) : Real.Angle) ≤ -c := by
  rw [hab]
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨p, hp, rfl⟩
  dsimp only
  rw [normalVector_add_pi, inner_neg_right]
  linarith only [hs p hp]

/-- A contact point on a cut line attains the opposite support value. -/
theorem le_supportValue_of_cut {s : Set Point} (hcomp : IsCompact s) {a b c : ℝ} {p : Point}
    (hab : ((b : ℝ) : Real.Angle) = ((a + Real.pi : ℝ) : Real.Angle)) (hp : p ∈ s)
    (hpc : inner ℝ p (normalVector (a : Real.Angle)) = c) :
    -c ≤ supportValue s ((b : ℝ) : Real.Angle) := by
  rw [hab]
  have h := inner_le_supportValue_of_isCompact hcomp hp ((a + Real.pi : ℝ) : Real.Angle)
  rw [normalVector_add_pi, inner_neg_right, hpc] at h
  linarith only [h]
end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Contacts
-/

@[expose] public section

noncomputable section

namespace MovingSofa

/-- The exposed edge at a normal direction, including singleton edges. -/
def exposedEdge (K : ConvexBody Point) (t : Real.Angle) : Set Point :=
  (K : Set Point) ∩ (supportingLineHalfPlane K t).1

/-- The positive and negative tangent endpoints of an exposed edge. -/
def edgeVertices (K : ConvexBody Point) (t : Real.Angle) : Point × Point :=
  let heights := (fun p ↦ inner ℝ p (tangentVector t)) '' exposedEdge K t
  (supportValue K t • normalVector t + sSup heights • tangentVector t,
    supportValue K t • normalVector t + sInf heights • tangentVector t)

/-- The intersection point of two supporting lines at nonparallel normal directions. -/
def supportingIntersection (K : ConvexBody Point) (a b : Real.Angle) : Point :=
  supportValue K a • normalVector a +
    ((supportValue K b - supportValue K a * (b - a).cos) / (b - a).sin) • tangentVector a

theorem exposedEdge_nonempty (K : ConvexBody Point) (t : Real.Angle) :
    (exposedEdge K t).Nonempty := by
  obtain ⟨x, hx, hxmax, _⟩ := K.isCompact.exists_sSup_image_eq_and_ge
    (f := fun x : Point ↦ inner ℝ x (normalVector t)) K.nonempty
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
  refine ⟨x, hx, ?_⟩
  simpa [supportingLineHalfPlane, normalLine, supportValue] using hxmax.symm

theorem convex_exposedEdge (K : ConvexBody Point) (t : Real.Angle) :
    Convex ℝ (exposedEdge K t) := by
  apply K.convex.inter
  intro x hx y hy a b ha hb hab
  change inner ℝ x (normalVector t) = supportValue K t at hx
  change inner ℝ y (normalVector t) = supportValue K t at hy
  change inner ℝ (a • x + b • y) (normalVector t) = supportValue K t
  rw [inner_add_left, inner_smul_left, inner_smul_left, hx, hy]
  simp only [RCLike.conj_to_real]
  rw [← add_mul, hab, one_mul]

theorem isConnected_exposedEdge (K : ConvexBody Point) (t : Real.Angle) :
    IsConnected (exposedEdge K t) :=
  (convex_exposedEdge K t).isConnected (exposedEdge_nonempty K t)

theorem supportingIntersection_inner_left (K : ConvexBody Point) (s t : ℝ) :
    inner ℝ (supportingIntersection K (s : Real.Angle) (t : Real.Angle))
      (normalVector (s : Real.Angle)) = supportValue K (s : Real.Angle) := by
  have htn : inner ℝ (tangentVector (s : Real.Angle)) (normalVector (s : Real.Angle)) = 0 := by
    rw [real_inner_comm, inner_normalVector_tangentVector]
  simp only [supportingIntersection, inner_add_left, real_inner_smul_left,
    inner_normalVector_self, htn, mul_one, mul_zero, add_zero]

theorem supportingIntersection_inner_right (K : ConvexBody Point) (s t : ℝ)
    (h : Real.sin (t - s) ≠ 0) :
    inner ℝ (supportingIntersection K (s : Real.Angle) (t : Real.Angle))
      (normalVector (t : Real.Angle)) = supportValue K (t : Real.Angle) := by
  have hn : normalVector (t : Real.Angle) =
      Real.cos (t - s) • normalVector (s : Real.Angle) +
      Real.sin (t - s) • tangentVector (s : Real.Angle) := by
    simpa only [add_sub_cancel] using normalVector_add_real s (t - s)
  rw [hn, inner_add_right, inner_smul_right, inner_smul_right,
    supportingIntersection_inner_left]
  simp only [supportingIntersection, inner_add_left, real_inner_smul_left,
    inner_normalVector_tangentVector, inner_tangentVector_self, mul_zero, mul_one, zero_add,
    ← Real.Angle.coe_sub, Real.Angle.cos_coe, Real.Angle.sin_coe]
  field_simp
  ring

theorem supportingIntersection_comm (K : ConvexBody Point) (s t : ℝ)
    (h : Real.sin (t - s) ≠ 0) :
    supportingIntersection K (s : Real.Angle) (t : Real.Angle) =
      supportingIntersection K (t : Real.Angle) (s : Real.Angle) := by
  have h' : Real.sin (s - t) ≠ 0 := by
    rw [show s - t = -(t - s) by ring, Real.sin_neg]
    exact neg_ne_zero.mpr h
  let p := supportingIntersection K (t : Real.Angle) (s : Real.Angle)
  have hp := supportingIntersection_inner_right K t s h'
  have hq := supportingIntersection_inner_left K t s
  change inner ℝ p (normalVector (s : Real.Angle)) = _ at hp
  change inner ℝ p (normalVector (t : Real.Angle)) = _ at hq
  have hn : normalVector (t : Real.Angle) =
      Real.cos (t - s) • normalVector (s : Real.Angle) +
      Real.sin (t - s) • tangentVector (s : Real.Angle) := by
    simpa only [add_sub_cancel] using normalVector_add_real s (t - s)
  rw [hn, inner_add_right, inner_smul_right, inner_smul_right, hp] at hq
  have ht : inner ℝ p (tangentVector (s : Real.Angle)) =
      (supportValue K (t : Real.Angle) - supportValue K (s : Real.Angle) *
        Real.cos (t - s)) / Real.sin (t - s) := by
    apply (eq_div_iff h).mpr
    linarith
  have heq := inner_normalVector_smul_add_inner_tangentVector_smul p (s : Real.Angle)
  rw [hp, ht] at heq
  simpa only [p, supportingIntersection, ← Real.Angle.coe_sub, Real.Angle.cos_coe,
    Real.Angle.sin_coe] using heq

/-- Every exposed edge of a compact convex body is compact. -/
theorem isCompact_exposedEdge (K : ConvexBody Point) (t : Real.Angle) :
    IsCompact (exposedEdge K t) :=
  K.isCompact.inter_right (isClosed_eq
    (continuous_id.inner continuous_const) continuous_const)

/-- The positive tangent endpoint belongs to its exposed edge. -/
theorem edgeVertices_fst_mem (K : ConvexBody Point) (t : Real.Angle) :
    (edgeVertices K t).1 ∈ exposedEdge K t := by
  obtain ⟨p, hp, hmax⟩ := (isCompact_exposedEdge K t).exists_sSup_image_eq
    (exposedEdge_nonempty K t)
    (f := fun p : Point ↦ inner ℝ p (tangentVector t))
    (continuous_id.inner continuous_const).continuousOn
  have hpnormal : inner ℝ p (normalVector t) = supportValue K t := hp.2
  have heq : (edgeVertices K t).1 = p := by
    change supportValue K t • normalVector t +
      sSup ((fun q ↦ inner ℝ q (tangentVector t)) '' exposedEdge K t) • tangentVector t = p
    rw [hmax, ← hpnormal]
    exact inner_normalVector_smul_add_inner_tangentVector_smul p t
  exact heq ▸ hp

/-- The negative tangent endpoint belongs to its exposed edge. -/
theorem edgeVertices_snd_mem (K : ConvexBody Point) (t : Real.Angle) :
    (edgeVertices K t).2 ∈ exposedEdge K t := by
  obtain ⟨p, hp, hmin⟩ := (isCompact_exposedEdge K t).exists_sInf_image_eq
    (exposedEdge_nonempty K t)
    (f := fun p : Point ↦ inner ℝ p (tangentVector t))
    (continuous_id.inner continuous_const).continuousOn
  have hpnormal : inner ℝ p (normalVector t) = supportValue K t := hp.2
  have heq : (edgeVertices K t).2 = p := by
    change supportValue K t • normalVector t +
      sInf ((fun q ↦ inner ℝ q (tangentVector t)) '' exposedEdge K t) • tangentVector t = p
    rw [hmin, ← hpnormal]
    exact inner_normalVector_smul_add_inner_tangentVector_smul p t
  exact heq ▸ hp

/-- A singleton exposed face is both of its tangent endpoints. -/
theorem edgeVertices_eq_of_exposedEdge_singleton {K : ConvexBody Point} {t : Real.Angle}
    {p : Point} (h : exposedEdge K t = {p}) : edgeVertices K t = (p, p) := by
  have h1 := edgeVertices_fst_mem K t
  have h2 := edgeVertices_snd_mem K t
  rw [h, Set.mem_singleton_iff] at h1 h2
  exact Prod.ext h1 h2

/-- The positive face vertex attains the largest tangent coordinate. -/
theorem inner_edgeVertices_fst_tangent (K : ConvexBody Point) (t : Real.Angle) :
    inner ℝ (edgeVertices K t).1 (tangentVector t) =
      sSup ((fun p ↦ inner ℝ p (tangentVector t)) '' exposedEdge K t) := by
  induction t using Real.Angle.induction_on with
  | _ t =>
    simp only [edgeVertices, inner_add_left, real_inner_smul_left,
      inner_normalVector_tangentVector, inner_tangentVector_self]
    ring

/-- The negative face vertex attains the smallest tangent coordinate. -/
theorem inner_edgeVertices_snd_tangent (K : ConvexBody Point) (t : Real.Angle) :
    inner ℝ (edgeVertices K t).2 (tangentVector t) =
      sInf ((fun p ↦ inner ℝ p (tangentVector t)) '' exposedEdge K t) := by
  induction t using Real.Angle.induction_on with
  | _ t =>
    simp only [edgeVertices, inner_add_left, real_inner_smul_left,
      inner_normalVector_tangentVector, inner_tangentVector_self]
    ring

private theorem exposedEdge_subset_segment_edgeVertices (K : ConvexBody Point)
    (t : Real.Angle) :
    exposedEdge K t ⊆ segment ℝ (edgeVertices K t).2 (edgeVertices K t).1 := by
  intro p hp
  let lo := (edgeVertices K t).2
  let hi := (edgeVertices K t).1
  let z := inner ℝ p (tangentVector t)
  let zlo := inner ℝ lo (tangentVector t)
  let zhi := inner ℝ hi (tangentVector t)
  have hbddBelow : BddBelow ((fun q ↦ inner ℝ q (tangentVector t)) '' exposedEdge K t) :=
    (isCompact_exposedEdge K t).image
      (continuous_id.inner continuous_const) |>.bddBelow
  have hbddAbove : BddAbove ((fun q ↦ inner ℝ q (tangentVector t)) '' exposedEdge K t) :=
    (isCompact_exposedEdge K t).image
      (continuous_id.inner continuous_const) |>.bddAbove
  have hzmem : z ∈ (fun q ↦ inner ℝ q (tangentVector t)) '' exposedEdge K t :=
    ⟨p, hp, rfl⟩
  have hzlo : zlo ≤ z := by
    dsimp only [zlo, z, lo]
    rw [inner_edgeVertices_snd_tangent]
    exact csInf_le hbddBelow hzmem
  have hzhi : z ≤ zhi := by
    dsimp only [zhi, z, hi]
    rw [inner_edgeVertices_fst_tangent]
    exact le_csSup hbddAbove hzmem
  by_cases hzh : zlo = zhi
  · have hz : z = zlo := le_antisymm (hzhi.trans_eq hzh.symm) hzlo
    have hpnormal : inner ℝ p (normalVector t) = supportValue K t := hp.2
    have hlonormal : inner ℝ lo (normalVector t) = supportValue K t :=
      (edgeVertices_snd_mem K t).2
    have hpl : p = lo := by
      rw [← inner_normalVector_smul_add_inner_tangentVector_smul p t,
        ← inner_normalVector_smul_add_inner_tangentVector_smul lo t,
        hpnormal, hlonormal]
      change inner ℝ p (tangentVector t) = inner ℝ lo (tangentVector t) at hz
      rw [hz]
    simpa only [lo, hi, hpl] using left_mem_segment ℝ lo hi
  · have hlt : zlo < zhi := lt_of_le_of_ne (hzlo.trans hzhi) hzh
    let u := (z - zlo) / (zhi - zlo)
    have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hzlo) (sub_nonneg.mpr hlt.le)
      · rw [div_le_one (sub_pos.mpr hlt)]
        linarith
    rw [segment_eq_image]
    refine ⟨u, hu, ?_⟩
    change (1 - u) • lo + u • hi = p
    have hpnormal : inner ℝ p (normalVector t) = supportValue K t := hp.2
    have hlonormal : inner ℝ lo (normalVector t) = supportValue K t :=
      (edgeVertices_snd_mem K t).2
    have hhinormal : inner ℝ hi (normalVector t) = supportValue K t :=
      (edgeVertices_fst_mem K t).2
    have hnormal : inner ℝ ((1 - u) • lo + u • hi) (normalVector t) =
        inner ℝ p (normalVector t) := by
      simp only [inner_add_left, real_inner_smul_left, hlonormal, hhinormal, hpnormal]
      ring
    have htangent : inner ℝ ((1 - u) • lo + u • hi) (tangentVector t) =
        inner ℝ p (tangentVector t) := by
      simp only [inner_add_left, real_inner_smul_left]
      change (1 - u) * zlo + u * zhi = z
      dsimp [u]
      field_simp [sub_ne_zero.mpr (ne_of_gt hlt)]
      ring
    rw [← inner_normalVector_smul_add_inner_tangentVector_smul
      ((1 - u) • lo + u • hi) t,
      ← inner_normalVector_smul_add_inner_tangentVector_smul p t,
      hnormal, htangent]

/-- An exposed face is the segment joining its two tangent-extreme vertices. -/
theorem exposedEdge_eq_segment_edgeVertices (K : ConvexBody Point)
    (t : Real.Angle) :
    exposedEdge K t = segment ℝ (edgeVertices K t).2 (edgeVertices K t).1 := by
  apply Set.Subset.antisymm (exposedEdge_subset_segment_edgeVertices K t)
  exact (convex_exposedEdge K t).segment_subset
    (edgeVertices_snd_mem K t) (edgeVertices_fst_mem K t)

/-- An exposed face determines the support value and both of its endpoint vertices. -/
theorem edgeVertices_eq_of_exposedEdge_eq (K L : ConvexBody Point) (u : Real.Angle)
    (h : exposedEdge K u = exposedEdge L u) : edgeVertices K u = edgeVertices L u := by
  obtain ⟨p, hp⟩ := exposedEdge_nonempty K u
  have hpL : p ∈ exposedEdge L u := h ▸ hp
  have hK : inner ℝ p (normalVector u) = supportValue K u := hp.2
  have hL : inner ℝ p (normalVector u) = supportValue L u := hpL.2
  simp only [edgeVertices, hK.symm.trans hL, h]

/-- A support-line intersection in the body is the negative endpoint at the later normal. -/
theorem supportingIntersection_eq_edgeVertices_snd_of_mem (K : ConvexBody Point) {a b : ℝ}
    (hab : 0 < b - a) (hpi : b - a < Real.pi)
    (hp : supportingIntersection K (a : Real.Angle) (b : Real.Angle) ∈ K) :
    supportingIntersection K (a : Real.Angle) (b : Real.Angle) =
      (edgeVertices K (b : Real.Angle)).2 := by
  let p := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  let e := (edgeVertices K (b : Real.Angle)).2
  have hsin : 0 < Real.sin (b - a) := Real.sin_pos_of_pos_of_lt_pi hab hpi
  have hsina : Real.sin (a - b) < 0 := by
    rw [show a - b = -(b - a) by ring, Real.sin_neg]
    exact neg_neg_of_pos hsin
  have hpa : inner ℝ p (normalVector (a : Real.Angle)) =
      supportValue K (a : Real.Angle) := supportingIntersection_inner_left K a b
  have hpb : inner ℝ p (normalVector (b : Real.Angle)) =
      supportValue K (b : Real.Angle) :=
    supportingIntersection_inner_right K a b hsin.ne'
  have hpedge : p ∈ exposedEdge K (b : Real.Angle) := ⟨hp, hpb⟩
  have heedge := edgeVertices_snd_mem K (b : Real.Angle)
  have hen : inner ℝ e (normalVector (b : Real.Angle)) =
      supportValue K (b : Real.Angle) := heedge.2
  have hpt : inner ℝ p (tangentVector (b : Real.Angle)) =
      inner ℝ e (tangentVector (b : Real.Angle)) := by
    rw [inner_edgeVertices_snd_tangent]
    apply le_antisymm
    · apply le_csInf ((exposedEdge_nonempty K _).image _)
      rintro _ ⟨q, hq, rfl⟩
      have hqa := inner_le_supportValue K hq.1 (a : Real.Angle)
      have hna : normalVector (a : Real.Angle) =
          Real.cos (a - b) • normalVector (b : Real.Angle) +
            Real.sin (a - b) • tangentVector (b : Real.Angle) := by
        simpa only [add_sub_cancel] using normalVector_add_real b (a - b)
      rw [← hpa, hna] at hqa
      simp only [inner_add_right, inner_smul_right] at hqa
      rw [hpb, hq.2] at hqa
      nlinarith
    · exact csInf_le ((isCompact_exposedEdge K _).image
        (continuous_id.inner continuous_const)).bddBelow ⟨p, hpedge, rfl⟩
  change p = e
  rw [← inner_normalVector_smul_add_inner_tangentVector_smul p (b : Real.Angle),
    ← inner_normalVector_smul_add_inner_tangentVector_smul e (b : Real.Angle), hpb, hen,
    hpt]

/-- A support-line intersection in the body is the positive endpoint at the earlier normal. -/
theorem supportingIntersection_eq_edgeVertices_fst_of_mem (K : ConvexBody Point) {a b : ℝ}
    (hab : 0 < b - a) (hpi : b - a < Real.pi)
    (hp : supportingIntersection K (a : Real.Angle) (b : Real.Angle) ∈ K) :
    supportingIntersection K (a : Real.Angle) (b : Real.Angle) =
      (edgeVertices K (a : Real.Angle)).1 := by
  let p := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  let e := (edgeVertices K (a : Real.Angle)).1
  have hsin : 0 < Real.sin (b - a) := Real.sin_pos_of_pos_of_lt_pi hab hpi
  have hpa : inner ℝ p (normalVector (a : Real.Angle)) =
      supportValue K (a : Real.Angle) := supportingIntersection_inner_left K a b
  have hpb : inner ℝ p (normalVector (b : Real.Angle)) =
      supportValue K (b : Real.Angle) :=
    supportingIntersection_inner_right K a b hsin.ne'
  have hpedge : p ∈ exposedEdge K (a : Real.Angle) := ⟨hp, hpa⟩
  have heedge := edgeVertices_fst_mem K (a : Real.Angle)
  have hen : inner ℝ e (normalVector (a : Real.Angle)) =
      supportValue K (a : Real.Angle) := heedge.2
  have hpt : inner ℝ p (tangentVector (a : Real.Angle)) =
      inner ℝ e (tangentVector (a : Real.Angle)) := by
    rw [inner_edgeVertices_fst_tangent]
    apply le_antisymm
    · exact le_csSup ((isCompact_exposedEdge K _).image
        (continuous_id.inner continuous_const)).bddAbove ⟨p, hpedge, rfl⟩
    · apply csSup_le ((exposedEdge_nonempty K _).image _)
      rintro _ ⟨q, hq, rfl⟩
      have hqb := inner_le_supportValue K hq.1 (b : Real.Angle)
      have hnb : normalVector (b : Real.Angle) =
          Real.cos (b - a) • normalVector (a : Real.Angle) +
            Real.sin (b - a) • tangentVector (a : Real.Angle) := by
        simpa only [add_sub_cancel] using normalVector_add_real a (b - a)
      rw [← hpb, hnb] at hqb
      simp only [inner_add_right, inner_smul_right] at hqb
      rw [hpa, hq.2] at hqb
      nlinarith
  change p = e
  rw [← inner_normalVector_smul_add_inner_tangentVector_smul p (a : Real.Angle),
    ← inner_normalVector_smul_add_inner_tangentVector_smul e (a : Real.Angle), hpa, hen,
    hpt]

/-- The first endpoint reaches the adjacent supporting-line intersection along a positive
tangent ray. -/
theorem supportingIntersection_eq_fst_add_pos_tangent
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    ∃ d : ℝ, 0 < d ∧ supportingIntersection K a b =
      (edgeVertices K (a : Real.Angle)).1 + d • tangentVector (a : Real.Angle) := by
  let O := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  let P := (edgeVertices K (a : Real.Angle)).1
  let d := inner ℝ (O - P) (tangentVector (a : Real.Angle))
  have hsin : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)
  have hOn : inner ℝ O (normalVector (a : Real.Angle)) = supportValue K a :=
    supportingIntersection_inner_left K a b
  have hPn : inner ℝ P (normalVector (a : Real.Angle)) = supportValue K a :=
    (edgeVertices_fst_mem K (a : Real.Angle)).2
  have hnormal : inner ℝ (O - P) (normalVector (a : Real.Angle)) = 0 := by
    rw [inner_sub_left, hOn, hPn, sub_self]
  have hdir : O = P + d • tangentVector (a : Real.Angle) := by
    rw [show O = P + (O - P) by abel, ← inner_normalVector_smul_add_inner_tangentVector_smul
      (O - P) (a : Real.Angle), hnormal, zero_smul, zero_add]
  have hdnonneg : 0 ≤ d := by
    have hOb : inner ℝ O (normalVector (b : Real.Angle)) = supportValue K b :=
      supportingIntersection_inner_right K a b hsin.ne'
    have hPb := inner_le_supportValue K (edgeVertices_fst_mem K (a : Real.Angle)).1
      (b : Real.Angle)
    change inner ℝ P (normalVector (b : Real.Angle)) ≤ supportValue K b at hPb
    have hnb : normalVector (b : Real.Angle) =
        Real.cos (b - a) • normalVector (a : Real.Angle) +
          Real.sin (b - a) • tangentVector (a : Real.Angle) := by
      simpa only [add_sub_cancel] using normalVector_add_real a (b - a)
    rw [← hOb, hdir, hnb, inner_add_left, inner_add_right, inner_smul_right,
      inner_smul_right, real_inner_smul_left, hPn] at hPb
    have htn : inner ℝ (tangentVector (a : Real.Angle))
        (normalVector (a : Real.Angle)) = 0 := by
      rw [real_inner_comm, inner_normalVector_tangentVector]
    simp only [inner_add_right, inner_smul_right, htn,
      inner_tangentVector_self, mul_zero, mul_one, zero_add] at hPb
    nlinarith
  have hdne : d ≠ 0 := by
    intro hd
    have hOP : O = P := by simpa [hd] using hdir
    have hOmem : O ∈ K := hOP ▸ (edgeVertices_fst_mem K _).1
    have hOQ := supportingIntersection_eq_edgeVertices_snd_of_mem K
      (sub_pos.mpr hab) (by linarith) hOmem
    exact hne (hOP.symm.trans hOQ)
  exact ⟨d, lt_of_le_of_ne hdnonneg (Ne.symm hdne), hdir⟩

/-- The second endpoint reaches the adjacent supporting-line intersection against a positive
tangent ray. -/
theorem supportingIntersection_eq_snd_sub_pos_tangent
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    ∃ d : ℝ, 0 < d ∧ supportingIntersection K a b =
      (edgeVertices K (b : Real.Angle)).2 - d • tangentVector (b : Real.Angle) := by
  let O := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  let Q := (edgeVertices K (b : Real.Angle)).2
  let d := inner ℝ (Q - O) (tangentVector (b : Real.Angle))
  have hsin : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)
  have hOn : inner ℝ O (normalVector (b : Real.Angle)) = supportValue K b :=
    supportingIntersection_inner_right K a b hsin.ne'
  have hQn : inner ℝ Q (normalVector (b : Real.Angle)) = supportValue K b :=
    (edgeVertices_snd_mem K (b : Real.Angle)).2
  have hnormal : inner ℝ (Q - O) (normalVector (b : Real.Angle)) = 0 := by
    rw [inner_sub_left, hQn, hOn, sub_self]
  have hdir : O = Q - d • tangentVector (b : Real.Angle) := by
    rw [show O = Q - (Q - O) by abel, ← inner_normalVector_smul_add_inner_tangentVector_smul
      (Q - O) (b : Real.Angle), hnormal, zero_smul, zero_add]
  have hdnonneg : 0 ≤ d := by
    have hOa : inner ℝ O (normalVector (a : Real.Angle)) = supportValue K a :=
      supportingIntersection_inner_left K a b
    have hQa := inner_le_supportValue K (edgeVertices_snd_mem K (b : Real.Angle)).1
      (a : Real.Angle)
    change inner ℝ Q (normalVector (a : Real.Angle)) ≤ supportValue K a at hQa
    have hna : normalVector (a : Real.Angle) =
        Real.cos (a - b) • normalVector (b : Real.Angle) +
          Real.sin (a - b) • tangentVector (b : Real.Angle) := by
      simpa only [add_sub_cancel] using normalVector_add_real b (a - b)
    rw [← hOa, hdir, hna, inner_sub_left, inner_add_right, inner_smul_right,
      inner_smul_right, real_inner_smul_left, hQn] at hQa
    have htn : inner ℝ (tangentVector (b : Real.Angle))
        (normalVector (b : Real.Angle)) = 0 := by
      rw [real_inner_comm, inner_normalVector_tangentVector]
    simp only [inner_add_right, inner_smul_right, htn,
      inner_tangentVector_self, mul_zero, mul_one, zero_add] at hQa
    have hsneg : Real.sin (a - b) < 0 := by
      rw [show a - b = -(b - a) by ring, Real.sin_neg]
      exact neg_neg_of_pos hsin
    nlinarith
  have hdne : d ≠ 0 := by
    intro hd
    have hOQ : O = Q := by simpa [hd] using hdir
    have hOmem : O ∈ K := hOQ ▸ (edgeVertices_snd_mem K _).1
    have hOP := supportingIntersection_eq_edgeVertices_fst_of_mem K
      (sub_pos.mpr hab) (by linarith) hOmem
    exact hne (hOP.symm.trans hOQ)
  exact ⟨d, lt_of_le_of_ne hdnonneg (Ne.symm hdne), hdir⟩

/-! ### Faces at a reversed normal direction -/

/-- A body bounded below in a normal direction, with the bound attained, has the opposite
support value in the reversed direction. -/
theorem supportValue_add_pi_eq_neg_of_forall_le {L : ConvexBody Point} {c t : ℝ} {p : Point}
    (hle : ∀ q ∈ (L : Set Point), c ≤ inner ℝ q (normalVector (t : Real.Angle)))
    (hp : p ∈ (L : Set Point)) (hpc : inner ℝ p (normalVector (t : Real.Angle)) = c) :
    supportValue L ((t + Real.pi : ℝ) : Real.Angle) = -c :=
  le_antisymm (supportValue_le_of_cut L.nonempty rfl hle)
    (le_supportValue_of_cut L.isCompact rfl hp hpc)

/-- The face at a reversed normal direction consists of the points attaining the attained
lower bound. -/
theorem exposedEdge_add_pi_eq_of_forall_le {L : ConvexBody Point} {c t : ℝ} {p : Point}
    (hle : ∀ q ∈ (L : Set Point), c ≤ inner ℝ q (normalVector (t : Real.Angle)))
    (hp : p ∈ (L : Set Point)) (hpc : inner ℝ p (normalVector (t : Real.Angle)) = c) :
    exposedEdge L ((t + Real.pi : ℝ) : Real.Angle) =
      {q | q ∈ (L : Set Point) ∧ inner ℝ q (normalVector (t : Real.Angle)) = c} := by
  have hsup := supportValue_add_pi_eq_neg_of_forall_le hle hp hpc
  ext q
  constructor
  · intro hq
    have h2 : inner ℝ q (normalVector ((t + Real.pi : ℝ) : Real.Angle)) =
      supportValue L ((t + Real.pi : ℝ) : Real.Angle) := hq.2
    rw [normalVector_add_pi, inner_neg_right, hsup] at h2
    exact ⟨hq.1, by linarith only [h2]⟩
  · rintro ⟨hqL, hqc⟩
    refine ⟨hqL, ?_⟩
    change inner ℝ q (normalVector ((t + Real.pi : ℝ) : Real.Angle)) = _
    rw [normalVector_add_pi, inner_neg_right, hsup, hqc]

/-! ### Faces between two supporting normals with a common contact point -/

/-- A point on two transverse supporting lines is their intersection. -/
theorem eq_supportingIntersection_of_mem_exposedEdge {L : ConvexBody Point} {a b : ℝ}
    {p : Point} (hsin : Real.sin (a - b) ≠ 0) (hpa : p ∈ exposedEdge L (a : Real.Angle))
    (hpb : p ∈ exposedEdge L (b : Real.Angle)) :
    p = supportingIntersection L (a : Real.Angle) (b : Real.Angle) := by
  have hsin' : Real.sin (b - a) ≠ 0 := by
    rw [show b - a = -(a - b) by ring, Real.sin_neg]
    exact neg_ne_zero.mpr hsin
  refine eq_of_inner_normalVector_eq hsin ?_ ?_
  · rw [supportingIntersection_inner_left]
    exact hpa.2
  · rw [supportingIntersection_inner_right L a b hsin']
    exact hpb.2

/-- Between two supporting normals less than a straight angle apart with a common contact
point, every intervening face is that point. -/
theorem exposedEdge_eq_singleton_of_mem_exposedEdge_of_mem_Ioo {L : ConvexBody Point}
    {a b s : ℝ} {p : Point} (hba : b < a + Real.pi) (hs : s ∈ Set.Ioo a b)
    (hpa : p ∈ exposedEdge L (a : Real.Angle)) (hpb : p ∈ exposedEdge L (b : Real.Angle)) :
    exposedEdge L (s : Real.Angle) = {p} := by
  have hab : a < b := hs.1.trans hs.2
  have hsba : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith only [hab]) (by linarith only [hba])
  have hsbs : 0 < Real.sin (b - s) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith only [hs.2]) (by linarith only [hba, hs.1])
  have hssa : 0 < Real.sin (s - a) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith only [hs.1]) (by linarith only [hba, hs.2])
  -- the positive combination of the two endpoint normals
  have hcomb : ∀ q : Point, Real.sin (b - s) * inner ℝ q (normalVector (a : Real.Angle)) +
      Real.sin (s - a) * inner ℝ q (normalVector (b : Real.Angle)) =
      Real.sin (b - a) * inner ℝ q (normalVector (s : Real.Angle)) := by
    intro q
    rw [inner_normalVector_real, inner_normalVector_real, inner_normalVector_real,
      Real.sin_sub, Real.sin_sub, Real.sin_sub]
    ring
  have hqa : ∀ q ∈ (L : Set Point), inner ℝ q (normalVector (a : Real.Angle)) ≤
      inner ℝ p (normalVector (a : Real.Angle)) := by
    intro q hq
    rw [hpa.2]
    exact inner_le_supportValue L hq _
  have hqb : ∀ q ∈ (L : Set Point), inner ℝ q (normalVector (b : Real.Angle)) ≤
      inner ℝ p (normalVector (b : Real.Angle)) := by
    intro q hq
    rw [hpb.2]
    exact inner_le_supportValue L hq _
  have hps : ∀ q ∈ (L : Set Point), inner ℝ q (normalVector (s : Real.Angle)) ≤
      inner ℝ p (normalVector (s : Real.Angle)) := by
    intro q hq
    have h1 := mul_le_mul_of_nonneg_left (hqa q hq) hsbs.le
    have h2 := mul_le_mul_of_nonneg_left (hqb q hq) hssa.le
    have h := add_le_add h1 h2
    rw [hcomb q, hcomb p] at h
    exact le_of_mul_le_mul_left (by linarith only [h]) hsba
  have hpsval : inner ℝ p (normalVector (s : Real.Angle)) = supportValue L (s : Real.Angle) :=
    le_antisymm (inner_le_supportValue L hpa.1 _) (csSup_le (L.nonempty.image _)
      (by rintro _ ⟨q, hq, rfl⟩; exact hps q hq))
  ext q
  simp only [Set.mem_singleton_iff]
  refine ⟨fun hq ↦ ?_, fun hq ↦ hq ▸ ⟨hpa.1, hpsval⟩⟩
  have hqs : inner ℝ q (normalVector (s : Real.Angle)) =
      inner ℝ p (normalVector (s : Real.Angle)) := by rw [hq.2, hpsval]
  have hsum : Real.sin (b - s) *
        (inner ℝ p (normalVector (a : Real.Angle)) - inner ℝ q (normalVector (a : Real.Angle))) +
      Real.sin (s - a) *
        (inner ℝ p (normalVector (b : Real.Angle)) - inner ℝ q (normalVector (b : Real.Angle)))
      = 0 := by
    have h1 := hcomb p
    have h2 := hcomb q
    rw [hqs] at h2
    linear_combination h1 - h2
  have hza : inner ℝ q (normalVector (a : Real.Angle)) =
      inner ℝ p (normalVector (a : Real.Angle)) := by
    nlinarith only [hsum, hsbs, hssa, hqa q hq.1, hqb q hq.1]
  have hzb : inner ℝ q (normalVector (b : Real.Angle)) =
      inner ℝ p (normalVector (b : Real.Angle)) := by
    nlinarith only [hsum, hsbs, hssa, hqa q hq.1, hqb q hq.1]
  have hsinab : Real.sin (a - b) ≠ 0 := by
    rw [show a - b = -(b - a) by ring, Real.sin_neg]
    exact neg_ne_zero.mpr hsba.ne'
  exact eq_of_inner_normalVector_eq hsinab hza hzb

end MovingSofa

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Geometry / Frame Calculus
-/

@[expose] public section

noncomputable section

namespace MovingSofa

theorem hasDerivAt_normalVector (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ normalVector (s : Real.Angle))
      (tangentVector (t : Real.Angle)) t := by
  have h : HasDerivAt (fun s : ℝ ↦ (![Real.cos s, Real.sin s] : Fin 2 → ℝ))
      (![-Real.sin t, Real.cos t] : Fin 2 → ℝ) t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact Real.hasDerivAt_cos t
    · exact Real.hasDerivAt_sin t
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm.hasFDerivAt.comp_hasDerivAt t h

theorem hasDerivAt_tangentVector (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ tangentVector (s : Real.Angle))
      (-normalVector (t : Real.Angle)) t := by
  have h : HasDerivAt (fun s : ℝ ↦ (![-Real.sin s, Real.cos s] : Fin 2 → ℝ))
      (![-Real.cos t, -Real.sin t] : Fin 2 → ℝ) t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (Real.hasDerivAt_sin t).neg
    · exact Real.hasDerivAt_cos t
  convert (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm.hasFDerivAt.comp_hasDerivAt t
    h using 1
  · rfl
  · ext i
    fin_cases i <;> rfl

/-- The angular unit-normal parametrization is one-Lipschitz. -/
theorem lipschitzWith_normalVector_real :
    LipschitzWith 1 (fun t : ℝ ↦ normalVector (t : Real.Angle)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t ↦ (hasDerivAt_normalVector t).differentiableAt)
  intro t
  rw [(hasDerivAt_normalVector t).deriv]
  change ‖tangentVector (t : Real.Angle)‖ ≤ (1 : ℝ)
  rw [norm_tangentVector]

/-- The angular unit-tangent parametrization is one-Lipschitz. -/
theorem lipschitzWith_tangentVector_real :
    LipschitzWith 1 (fun t : ℝ ↦ tangentVector (t : Real.Angle)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t ↦ (hasDerivAt_tangentVector t).differentiableAt)
  intro t
  rw [(hasDerivAt_tangentVector t).deriv]
  change ‖-normalVector (t : Real.Angle)‖ ≤ (1 : ℝ)
  rw [norm_neg, norm_normalVector_real]

/-- A combination of the rotating frame whose coefficients are globally Lipschitz and bounded on a
set is Lipschitz on that set. -/
theorem lipschitzOnWith_frameCombination {f g : ℝ → ℝ} {C M : ℝ} {D : NNReal} {s : Set ℝ}
    (hD : 2 * (C + M) ≤ (D : ℝ)) (hM : 0 ≤ M)
    (hf : ∀ x y : ℝ, |f x - f y| ≤ C * |x - y|) (hg : ∀ x y : ℝ, |g x - g y| ≤ C * |x - y|)
    (hfM : ∀ x ∈ s, |f x| ≤ M) (hgM : ∀ x ∈ s, |g x| ≤ M) :
    LipschitzOnWith D (fun x : ℝ ↦ f x • normalVector (x : Real.Angle) +
      g x • tangentVector (x : Real.Angle)) s := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  have hframe (u v : ℝ) : dist (normalVector (u : Real.Angle)) (normalVector (v : Real.Angle)) ≤
      |u - v| ∧ dist (tangentVector (u : Real.Angle)) (tangentVector (v : Real.Angle)) ≤
        |u - v| := by
    constructor
    · simpa [Real.dist_eq] using lipschitzWith_normalVector_real.dist_le_mul u v
    · simpa [Real.dist_eq] using lipschitzWith_tangentVector_real.dist_le_mul u v
  have hpair (p q : ℝ) (u w : Point) (hu : ‖u‖ = 1) (hq : |q| ≤ M)
      (huw : dist u w ≤ |x - y|) : dist (p • u) (q • w) ≤ |p - q| + M * |x - y| := by
    have h1 : dist (p • u) (q • u) ≤ |p - q| := by
      simpa [hu, Real.dist_eq] using dist_pair_smul p q u
    have h2 : dist (q • u) (q • w) ≤ M * |x - y| := by
      refine (dist_smul_pair q u w).trans ?_
      rw [Real.dist_eq, sub_zero]
      exact mul_le_mul hq huw dist_nonneg hM
    exact (dist_triangle _ _ _).trans (add_le_add h1 h2)
  have h1 := hpair (f x) (f y) (normalVector (x : Real.Angle)) (normalVector (y : Real.Angle))
    (norm_normalVector_real x) (hfM y hy) (hframe x y).1
  have h2 := hpair (g x) (g y) (tangentVector (x : Real.Angle)) (tangentVector (y : Real.Angle))
    (norm_tangentVector _) (hgM y hy) (hframe x y).2
  have htri := dist_add_add_le (f x • normalVector (x : Real.Angle))
    (g x • tangentVector (x : Real.Angle)) (f y • normalVector (y : Real.Angle))
    (g y • tangentVector (y : Real.Angle))
  have hfxy := hf x y
  have hgxy := hg x y
  have hd : 2 * (C + M) * |x - y| ≤ (D : ℝ) * |x - y| :=
    mul_le_mul_of_nonneg_right hD (abs_nonneg _)
  rw [Real.dist_eq]
  linarith

/-- The angular derivative of a fixed normal projection is its tangent projection. -/
theorem hasDerivAt_inner_normalVector (A : Point) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ inner ℝ A (normalVector (u : Real.Angle)))
      (inner ℝ A (tangentVector (t : Real.Angle))) t := by
  simpa using (hasDerivAt_const t A).inner ℝ (hasDerivAt_normalVector t)

/-- A contact point in a normal direction has the support derivative as tangent coordinate. -/
theorem exists_contact_of_hasDerivAt {s : Set Point} (hcomp : IsCompact s)
    (hne : s.Nonempty) {t d : ℝ}
    (hd : HasDerivAt (fun u : ℝ ↦ supportValue s (u : Real.Angle)) d t) :
    ∃ A ∈ s, inner ℝ A (normalVector (t : Real.Angle)) = supportValue s (t : Real.Angle) ∧
      inner ℝ A (tangentVector (t : Real.Angle)) = d := by
  obtain ⟨A, hA, hmax, -⟩ := hcomp.exists_sSup_image_eq_and_ge
    (f := fun p : Point ↦ inner ℝ p (normalVector (t : Real.Angle))) hne
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hAt : inner ℝ A (normalVector (t : Real.Angle)) = supportValue s (t : Real.Angle) := by
    simpa only [supportValue] using hmax.symm
  refine ⟨A, hA, hAt, ?_⟩
  set F : ℝ → ℝ := fun u ↦ supportValue s (u : Real.Angle) -
    inner ℝ A (normalVector (u : Real.Angle)) with hF
  have hFmin : IsLocalMin F t := by
    filter_upwards with u
    have h1 : inner ℝ A (normalVector (u : Real.Angle)) ≤ supportValue s (u : Real.Angle) :=
      inner_le_supportValue_of_isCompact hcomp hA _
    simp only [hF, hAt, sub_self]
    linarith
  have hFderiv : HasDerivAt F (d - inner ℝ A (tangentVector (t : Real.Angle))) t :=
    hd.sub (hasDerivAt_inner_normalVector A t)
  have := hFmin.hasDerivAt_eq_zero hFderiv
  linarith
end MovingSofa

end

end

end
