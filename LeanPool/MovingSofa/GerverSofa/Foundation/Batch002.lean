/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import Aesop
public import LeanPool.MovingSofa.GerverSofa.Foundation.Batch001
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Topology.Instances.Real.Lemmas
/-!
# Gerver sofa dependency batch

* `SE2`.
* `SupportingHallway`.
* `Systems`.
* `Boxes`.
* `Geometry`.
-/

@[expose] public section

noncomputable section


section

/-!
# Orientation-preserving rigid motions of the plane

An element is represented by `(c,s,tₓ,tᵧ)` with `c²+s²=1`.  Its linear
part is the rotation matrix `[[c,-s],[s,c]]`, hence every value is an element
of `SE(2)` and not an arbitrary affine equivalence.
-/

@[expose] public section

namespace GerverSofa

/-- An orientation-preserving planar rigid motion represented by rotation and translation. -/
structure SE2 where
  /-- The cosine coefficient of the rotation. -/
  c : ℝ
  /-- The sine coefficient of the rotation. -/
  s : ℝ
  /-- The horizontal translation component. -/
  tx : ℝ
  /-- The vertical translation component. -/
  ty : ℝ
  unit : c * c + s * s = 1

namespace SE2

/-- Action of an orientation-preserving rigid motion on the plane. -/
def act (g : SE2) (p : Point) : Point :=
  (g.c * p.1 - g.s * p.2 + g.tx,
   g.s * p.1 + g.c * p.2 + g.ty)

/-- Identity element. -/
def one : SE2 where
  c := 1
  s := 0
  tx := 0
  ty := 0
  unit := by norm_num

/-- Inverse orientation-preserving rigid motion. -/
def inv (g : SE2) : SE2 where
  c := g.c
  s := -g.s
  tx := -(g.c * g.tx + g.s * g.ty)
  ty := g.s * g.tx - g.c * g.ty
  unit := by nlinarith [g.unit]

@[simp] theorem one_act (p : Point) : one.act p = p := by
  rcases p with ⟨x, y⟩
  simp [one, act]

@[simp] theorem inv_act_act (g : SE2) (p : Point) :
    g.inv.act (g.act p) = p := by
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · dsimp [act, inv]
    linear_combination x * g.unit
  · dsimp [act, inv]
    linear_combination y * g.unit

@[simp] theorem act_inv_act (g : SE2) (p : Point) :
    g.act (g.inv.act p) = p := by
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · dsimp [act, inv]
    linear_combination (x - g.tx) * g.unit
  · dsimp [act, inv]
    linear_combination (y - g.ty) * g.unit

/-- Componentwise continuity is the topology-free representation of a path
in `SE(2)` used by the formal moving-sofa definition. -/
def ContinuousPath (g : ℝ → SE2) : Prop :=
  Continuous (fun t => (g t).c) ∧
  Continuous (fun t => (g t).s) ∧
  Continuous (fun t => (g t).tx) ∧
  Continuous (fun t => (g t).ty)

/-- Inversion preserves continuous `SE(2)` paths. -/
theorem continuousPath_inv {g : ℝ → SE2} (hg : ContinuousPath g) :
    ContinuousPath (fun t => (g t).inv) := by
  rcases hg with ⟨hc, hs, htx, hty⟩
  refine ⟨hc, hs.neg, ?_, ?_⟩
  · exact ((hc.mul htx).add (hs.mul hty)).neg
  · exact (hs.mul htx).sub (hc.mul hty)

end SE2
end GerverSofa

end

end

section

/-!
# Supporting hallway and inverse motion
-/

@[expose] public section

namespace GerverSofa

/-- World-frame hallway obtained from the standard hallway by `frame`. -/
def supportingHallway (frame : SE2) : Set Point :=
  frame.act '' hallway

/-- Membership in a supporting hallway is equivalent to standard-hallway
membership after applying the inverse frame. -/
theorem mem_supportingHallway_iff (frame : SE2) (q : Point) :
    q ∈ supportingHallway frame ↔ frame.inv.act q ∈ hallway := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    simpa using hp
  · intro hq
    refine ⟨frame.inv.act q, hq, ?_⟩
    exact frame.act_inv_act q

/-- Set-level version of `mem_supportingHallway_iff`. -/
theorem inv_image_subset_hallway_of_subset_supporting
    (frame : SE2) (S : Set Point)
    (hS : S ⊆ supportingHallway frame) :
    frame.inv.act '' S ⊆ hallway := by
  rintro p ⟨q, hqS, rfl⟩
  exact (mem_supportingHallway_iff frame q).1 (hS hqS)

end GerverSofa

end

end

section

/-!
# The concrete reduced and 22-dimensional Romik systems

These are direct Lean transcriptions of equations (F1)--(F4) and of the
independent equations (27)--(39), (41), (43) used by the companion verifier.
-/

@[expose] public section

namespace GerverSofa

noncomputable section

namespace Reduced

/-- The four real parameters of the reduced Gerver equations. -/
structure Params where
  /-- The first scalar parameter in the reduced equations. -/
  a : ℝ
  /-- The second scalar parameter in the reduced equations. -/
  b : ℝ
  /-- The first switching angle. -/
  phi : ℝ
  /-- The second switching angle. -/
  theta : ℝ

/-- Four-dimensional reduced switching system. -/
def system (p : Params) : Fin 4 → ℝ :=
  let cp := Real.cos p.phi
  let sp := Real.sin p.phi
  let ct := Real.cos p.theta
  let st := Real.sin p.theta
  let delta := p.theta - p.phi
  ![
    p.a * (ct - cp) - 2 * p.b * sp + (delta - 1) * ct - st + cp + sp,
    p.a * (3 * st + sp) - 2 * p.b * cp + 3 * (delta - 1) * st + 3 * ct - sp + cp,
    p.a * cp - sp - (1 / 2 : ℝ) + (1 / 2 : ℝ) * cp - p.b * sp,
    p.a + Real.pi / 2 - p.phi - p.theta - p.b
      + (1 / 2 : ℝ) * delta * (1 + p.a) + (1 / 4 : ℝ) * delta * delta
  ]

/-- The proposition that all four reduced equations vanish. -/
def Equations (p : Params) : Prop := system p = 0

end Reduced

namespace Romik

/-- Translation, phase, and switching-angle parameters of the five Romik branches. -/
structure Params where
  /-- Horizontal translation coefficient for phase 1. -/
  k11 : ℝ
  /-- Vertical translation coefficient for phase 1. -/
  k12 : ℝ
  /-- Horizontal translation coefficient for phase 2. -/
  k21 : ℝ
  /-- Vertical translation coefficient for phase 2. -/
  k22 : ℝ
  /-- Horizontal translation coefficient for phase 3. -/
  k31 : ℝ
  /-- Vertical translation coefficient for phase 3. -/
  k32 : ℝ
  /-- Horizontal translation coefficient for phase 4. -/
  k41 : ℝ
  /-- Vertical translation coefficient for phase 4. -/
  k42 : ℝ
  /-- Horizontal translation coefficient for phase 5. -/
  k51 : ℝ
  /-- Vertical translation coefficient for phase 5. -/
  k52 : ℝ
  /-- Coefficient 1 in the phase 1 closed formula. -/
  a1 : ℝ
  /-- Coefficient 2 in the phase 1 closed formula. -/
  a2 : ℝ
  /-- Coefficient 1 in the phase 2 closed formula. -/
  b1 : ℝ
  /-- Coefficient 2 in the phase 2 closed formula. -/
  b2 : ℝ
  /-- Coefficient 1 in the phase 3 closed formula. -/
  c1 : ℝ
  /-- Coefficient 2 in the phase 3 closed formula. -/
  c2 : ℝ
  /-- Coefficient 1 in the phase 4 closed formula. -/
  d1 : ℝ
  /-- Coefficient 2 in the phase 4 closed formula. -/
  d2 : ℝ
  /-- Coefficient 1 in the phase 5 closed formula. -/
  e1 : ℝ
  /-- Coefficient 2 in the phase 5 closed formula. -/
  e2 : ℝ
  /-- First switching angle. -/
  phi : ℝ
  /-- Second switching angle. -/
  theta : ℝ

/-- Rotation of a body-frame vector into the world frame. -/
def rot (t : ℝ) (z : Point) : Point :=
  (Real.cos t * z.1 - Real.sin t * z.2,
   Real.sin t * z.1 + Real.cos t * z.2)

/-- Translate a point by the two specified coordinate offsets. -/
def addK (r : Point) (kx ky : ℝ) : Point := (r.1 + kx, r.2 + ky)

/-- Phase 1 of the five-phase Gerver path. -/
def path1 (p : Params) (t : ℝ) : Point :=
  let z : Point :=
    (p.a1 * Real.cos t + p.a2 * Real.sin t - 1,
     -p.a2 * Real.cos t + p.a1 * Real.sin t - 1 / 2)
  addK (rot t z) p.k11 p.k12

/-- Phase 2 of the five-phase Gerver path. -/
def path2 (p : Params) (t : ℝ) : Point :=
  let z : Point :=
    (-(1 / 4 : ℝ) * t * t + p.b1 * t + p.b2,
     (1 / 2 : ℝ) * t - p.b1 - 1)
  addK (rot t z) p.k21 p.k22

/-- Phase 3 of the five-phase Gerver path. -/
def path3 (p : Params) (t : ℝ) : Point :=
  addK (rot t (p.c1 - t, p.c2 + t)) p.k31 p.k32

/-- Phase 4 of the five-phase Gerver path. -/
def path4 (p : Params) (t : ℝ) : Point :=
  let z : Point :=
    (-(1 / 2 : ℝ) * t + p.d1 - 1,
     -(1 / 4 : ℝ) * t * t + p.d1 * t + p.d2)
  addK (rot t z) p.k41 p.k42

/-- Phase 5 of the five-phase Gerver path. -/
def path5 (p : Params) (t : ℝ) : Point :=
  let z : Point :=
    (p.e1 * Real.cos t + p.e2 * Real.sin t - 1 / 2,
     -p.e2 * Real.cos t + p.e1 * Real.sin t - 1)
  addK (rot t z) p.k51 p.k52

/-- Body-frame derivative coefficients `(alpha,beta)` on phase 1. -/
def alphaBeta1 (p : Params) (t : ℝ) : Point :=
  (-2 * p.a1 * Real.sin t + 2 * p.a2 * Real.cos t + 1 / 2,
   2 * p.a1 * Real.cos t + 2 * p.a2 * Real.sin t - 1)

/-- Body-frame velocity coordinates for phase 2. -/
def alphaBeta2 (p : Params) (t : ℝ) : Point :=
  (1 + 2 * p.b1 - t,
   -(1 / 4 : ℝ) * t * t + p.b1 * t + p.b2 + 1 / 2)

/-- Body-frame velocity coordinates for phase 3. -/
def alphaBeta3 (p : Params) (t : ℝ) : Point :=
  (-1 - p.c2 - t, 1 + p.c1 - t)

/-- Body-frame velocity coordinates for phase 4. -/
def alphaBeta4 (p : Params) (t : ℝ) : Point :=
  ((1 / 4 : ℝ) * t * t - p.d1 * t - p.d2 - 1 / 2,
   2 * p.d1 - 1 - t)

/-- Body-frame velocity coordinates for phase 5. -/
def alphaBeta5 (p : Params) (t : ℝ) : Point :=
  (1 - 2 * p.e1 * Real.sin t + 2 * p.e2 * Real.cos t,
   2 * p.e1 * Real.cos t + 2 * p.e2 * Real.sin t - 1 / 2)

/-- Rotate body-frame velocity coordinates into the world frame. -/
def pathPrimeFromAB (t : ℝ) (ab : Point) : Point := rot t ab

/-- World-frame velocity formula for phase 1. -/
def pathPrime1 (p : Params) (t : ℝ) : Point := pathPrimeFromAB t (alphaBeta1 p t)
/-- World-frame velocity formula for phase 2. -/
def pathPrime2 (p : Params) (t : ℝ) : Point := pathPrimeFromAB t (alphaBeta2 p t)
/-- World-frame velocity formula for phase 3. -/
def pathPrime3 (p : Params) (t : ℝ) : Point := pathPrimeFromAB t (alphaBeta3 p t)

/-- Romik's 22 independent scalar equations. -/
def system (p : Params) : Fin 22 → ℝ :=
  let halfPi := Real.pi / 2
  let quarterPi := Real.pi / 4
  let eta := halfPi - p.theta
  let tau := halfPi - p.phi
  let x1phi := path1 p p.phi
  let x2phi := path2 p p.phi
  let v1phi := pathPrime1 p p.phi
  let v2phi := pathPrime2 p p.phi
  let x2theta := path2 p p.theta
  let x3theta := path3 p p.theta
  let v2theta := pathPrime2 p p.theta
  let v3theta := pathPrime3 p p.theta
  let x3eta := path3 p eta
  let x4eta := path4 p eta
  let x4tau := path4 p tau
  let x5tau := path5 p tau
  let abEta := alphaBeta3 p eta
  let bEta : Point :=
    (x3eta.1 - abEta.1 * Real.sin eta,
     x3eta.2 + abEta.1 * Real.cos eta)
  ![
    p.e1 - p.a1,
    p.e2 + p.a2,
    p.d1 + p.b1 - quarterPi,
    p.d2 - p.b2 - quarterPi * (2 * p.b1 - quarterPi),
    p.c2 - p.c1 + halfPi,
    p.k11 - 1 + p.a1,
    p.k12 - 1 / 4,
    p.a2 + 1 / 4,
    x1phi.1 - x2phi.1,
    x1phi.2 - x2phi.2,
    v1phi.1 - v2phi.1,
    v1phi.2 - v2phi.2,
    x2theta.1 - x3theta.1,
    x2theta.2 - x3theta.2,
    v2theta.1 - v3theta.1,
    v2theta.2 - v3theta.2,
    x3eta.1 - x4eta.1,
    x3eta.2 - x4eta.2,
    x4tau.1 - x5tau.1,
    x4tau.2 - x5tau.2,
    x1phi.1 - bEta.1,
    x1phi.2 - bEta.2
  ]

/-- The proposition that all 22 independent equations vanish. -/
def Equations (p : Params) : Prop := system p = 0

end Romik

namespace Romik

/-- The physical five-phase path on `[0,π/2]`.  At a switching angle either
adjacent formula may be chosen; the certified matching equations prove they
coincide. -/
def path (p : Params) (t : ℝ) : Point :=
  let eta := Real.pi / 2 - p.theta
  let tau := Real.pi / 2 - p.phi
  if t ≤ p.phi then path1 p t
  else if t ≤ p.theta then path2 p t
  else if t ≤ eta then path3 p t
  else if t ≤ tau then path4 p t
  else path5 p t

/-- Linear normalization from unit time to physical rotation angle. -/
def angle (u : ℝ) : ℝ := u * (Real.pi / 2)

/-- Standard-to-world frame `q ↦ x(t)+R_t q` for normalized time. -/
def frame (p : Params) (u : ℝ) : SE2 :=
  let t := angle u
  let x := path p t
  { c := Real.cos t
    s := Real.sin t
    tx := x.1
    ty := x.2
    unit := by nlinarith [Real.sin_sq_add_cos_sq t] }

end Romik

namespace Romik

@[simp] theorem angle_zero : angle 0 = 0 := by
  simp [angle]

@[simp] theorem angle_one : angle 1 = Real.pi / 2 := by
  simp [angle]

/-- The normalized physical angle depends continuously on time. -/
theorem continuous_angle : Continuous angle := by
  unfold angle
  fun_prop

/-- Continuity of the five-phase path implies componentwise continuity of the
supporting `SE(2)` frame. -/
theorem continuousPath_frame_of_path
    (p : Params) (hpath : Continuous (path p)) :
    SE2.ContinuousPath (frame p) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Continuous (fun u : ℝ => Real.cos (angle u))
    simpa [Function.comp_def] using (Real.continuous_cos.comp continuous_angle)
  · change Continuous (fun u : ℝ => Real.sin (angle u))
    simpa [Function.comp_def] using (Real.continuous_sin.comp continuous_angle)
  · change Continuous (fun u : ℝ => (path p (angle u)).1)
    have hp : Continuous (fun u : ℝ => path p (angle u)) := by
      simpa [Function.comp_def] using (hpath.comp continuous_angle)
    exact hp.fst
  · change Continuous (fun u : ℝ => (path p (angle u)).2)
    have hp : Continuous (fun u : ℝ => path p (angle u)) := by
      simpa [Function.comp_def] using (hpath.comp continuous_angle)
    exact hp.snd

end Romik

namespace Romik

/-! ## Continuity from the independent matching equations -/

/-- Ordering data needed to read the five branches in their intended order. -/
structure SwitchOrder (p : Params) : Prop where
  phi_le_theta : p.phi ≤ p.theta
  theta_le_eta : p.theta ≤ Real.pi / 2 - p.theta
  eta_le_tau : Real.pi / 2 - p.theta ≤ Real.pi / 2 - p.phi

private theorem continuous_path1 (p : Params) : Continuous (path1 p) := by
  unfold path1 addK rot
  fun_prop

private theorem continuous_path2 (p : Params) : Continuous (path2 p) := by
  unfold path2 addK rot
  fun_prop

private theorem continuous_path3 (p : Params) : Continuous (path3 p) := by
  unfold path3 addK rot
  fun_prop

private theorem continuous_path4 (p : Params) : Continuous (path4 p) := by
  unfold path4 addK rot
  fun_prop

private theorem continuous_path5 (p : Params) : Continuous (path5 p) := by
  unfold path5 addK rot
  fun_prop

/-- Equation (35), extracted from the direct 22D system. -/
theorem match_path12_of_equations {p : Params} (heq : Equations p) :
    path1 p p.phi = path2 p p.phi := by
  have h8 := congrFun heq (8 : Fin 22)
  have h9 := congrFun heq (9 : Fin 22)
  simp [system] at h8 h9
  apply Prod.ext <;> linarith

/-- Equation (37), extracted from the direct 22D system. -/
theorem match_path23_of_equations {p : Params} (heq : Equations p) :
    path2 p p.theta = path3 p p.theta := by
  have h12 := congrFun heq (12 : Fin 22)
  have h13 := congrFun heq (13 : Fin 22)
  simp [system] at h12 h13
  apply Prod.ext <;> linarith

/-- Equation (39), extracted from the direct 22D system. -/
theorem match_path34_of_equations {p : Params} (heq : Equations p) :
    path3 p (Real.pi / 2 - p.theta) =
      path4 p (Real.pi / 2 - p.theta) := by
  have h16 := congrFun heq (16 : Fin 22)
  have h17 := congrFun heq (17 : Fin 22)
  simp [system] at h16 h17
  apply Prod.ext <;> linarith

/-- Equation (41), extracted from the direct 22D system. -/
theorem match_path45_of_equations {p : Params} (heq : Equations p) :
    path4 p (Real.pi / 2 - p.phi) =
      path5 p (Real.pi / 2 - p.phi) := by
  have h18 := congrFun heq (18 : Fin 22)
  have h19 := congrFun heq (19 : Fin 22)
  simp [system] at h18 h19
  apply Prod.ext <;> linarith

/-- The four positional matching equations make the literal nested-`if`
five-phase path continuous whenever its switches are ordered. -/
theorem continuous_path_of_order_and_equations
    {p : Params} (hord : SwitchOrder p) (heq : Equations p) :
    Continuous (path p) := by
  have h12 := match_path12_of_equations heq
  have h23 := match_path23_of_equations heq
  have h34 := match_path34_of_equations heq
  have h45 := match_path45_of_equations heq
  have hc45 : Continuous
      (fun t : ℝ =>
        if t ≤ Real.pi / 2 - p.phi then path4 p t else path5 p t) := by
    exact (continuous_path4 p).if_le (continuous_path5 p)
      continuous_id continuous_const (by
        intro t ht
        subst t
        exact h45)
  have hc345 : Continuous
      (fun t : ℝ =>
        if t ≤ Real.pi / 2 - p.theta then path3 p t
        else if t ≤ Real.pi / 2 - p.phi then path4 p t else path5 p t) := by
    exact (continuous_path3 p).if_le hc45
      continuous_id continuous_const (by
        intro t ht
        subst t
        rw [ite_eq_left hord.eta_le_tau]
        exact h34)
  have hc2345 : Continuous
      (fun t : ℝ =>
        if t ≤ p.theta then path2 p t
        else if t ≤ Real.pi / 2 - p.theta then path3 p t
        else if t ≤ Real.pi / 2 - p.phi then path4 p t else path5 p t) := by
    exact (continuous_path2 p).if_le hc345
      continuous_id continuous_const (by
        intro t ht
        subst t
        rw [ite_eq_left hord.theta_le_eta]
        exact h23)
  have hc12345 : Continuous
      (fun t : ℝ =>
        if t ≤ p.phi then path1 p t
        else if t ≤ p.theta then path2 p t
        else if t ≤ Real.pi / 2 - p.theta then path3 p t
        else if t ≤ Real.pi / 2 - p.phi then path4 p t else path5 p t) := by
    exact (continuous_path1 p).if_le hc2345
      continuous_id continuous_const (by
        intro t ht
        subst t
        rw [ite_eq_left hord.phi_le_theta]
        exact h12)
  unfold path
  exact hc12345

end Romik

end
end GerverSofa

end

end

section

/-!
# Exact real boxes used by the Krawczyk certificates

Every endpoint is written as an exact integer quotient.  There are no binary
floating-point constants in these definitions.
-/

@[expose] public section

noncomputable section

namespace GerverSofa

/-- Interpret an integer numerator and natural denominator as a real quotient. -/
def qR (n : Int) (d : Nat) : ℝ := (n : ℝ) / (d : ℝ)

namespace Reduced

/-- Input box `X_a × X_b × X_phi × X_theta`. -/
def box : Set Params :=
  {p |
    qR 1888531216873 20000000000000 ≤ p.a ∧ p.a ≤ qR 4721328042183 50000000000000 ∧
    qR 69960186366677 50000000000000 ≤ p.b ∧ p.b ≤ qR 34980093183339 25000000000000 ∧
    qR 122429264969 3125000000000 ≤ p.phi ∧ p.phi ≤ qR 3917736479009 100000000000000 ∧
    qR 2129067216821 3125000000000 ≤ p.theta ∧ p.theta ≤ qR 68130150938273 100000000000000}

end Reduced

namespace Romik

/-- The direct 22-dimensional box `Y × Phi × Theta`. -/
def box : Set Params :=
  {p |
    qR (-21032242207268875141628571849) 100000000000000000000000000000 ≤ p.k11 ∧ p.k11 ≤ qR
      (-21032242207268875141608571849) 100000000000000000000000000000 ∧
    qR 2499999999999999999999 10000000000000000000000 ≤ p.k12 ∧ p.k12 ≤ qR 2500000000000000000001
      10000000000000000000000 ∧
    qR (-91917929277159332227479610289) 100000000000000000000000000000 ≤ p.k21 ∧ p.k21 ≤ qR
      (-91917929277159332227459610289) 100000000000000000000000000000 ∧
    qR 29525413734425341573853797657 62500000000000000000000000000 ≤ p.k22 ∧ p.k22 ≤ qR
      29525413734425341573866297657 62500000000000000000000000000 ∧
    qR (-15344080735756291713875357283) 25000000000000000000000000000 ≤ p.k31 ∧ p.k31 ≤ qR
      (-15344080735756291713870357283) 25000000000000000000000000000 ∧
    qR 17792529580064437214538861001 20000000000000000000000000000 ≤ p.k32 ∧ p.k32 ≤ qR
      17792529580064437214542861001 20000000000000000000000000000 ∧
    qR (-15417358304445500741761623987) 50000000000000000000000000000 ≤ p.k41 ∧ p.k41 ≤ qR
      (-15417358304445500741751623987) 50000000000000000000000000000 ∧
    qR 29525413734425341573853797657 62500000000000000000000000000 ≤ p.k42 ∧ p.k42 ≤ qR
      29525413734425341573866297657 62500000000000000000000000000 ∧
    qR (-20344080735756291713874857283) 20000000000000000000000000000 ≤ p.k51 ∧ p.k51 ≤ qR
      (-20344080735756291713870857283) 20000000000000000000000000000 ∧
    qR 2499999999999999999999 10000000000000000000000 ≤ p.k52 ∧ p.k52 ≤ qR 2500000000000000000001
      10000000000000000000000 ∧
    qR 2420644844145377502832171437 2000000000000000000000000000 ≤ p.a1 ∧ p.a1 ≤ qR
      2420644844145377502832571437 2000000000000000000000000000 ∧
    qR (-2500000000000000000001) 10000000000000000000000 ≤ p.a2 ∧ p.a2 ≤ qR
      (-2499999999999999999999) 10000000000000000000000 ∧
    qR (-52762459802678462416060380937) 100000000000000000000000000000 ≤ p.b1 ∧ p.b1 ≤ qR
      (-52762459802678462416040380937) 100000000000000000000000000000 ∧
    qR 92025838516063762289360579501 100000000000000000000000000000 ≤ p.b2 ∧ p.b2 ≤ qR
      92025838516063762289380579501 100000000000000000000000000000 ∧
    qR 313022761424232933776114655193 500000000000000000000000000000 ≤ p.c1 ∧ p.c1 ≤ qR
      313022761424232933776214655193 500000000000000000000000000000 ∧
    qR (-151160128631428920268654781) 160000000000000000000000000 ≤ p.c2 ∧ p.c2 ≤ qR
      (-151160128631428920268622781) 160000000000000000000000000 ∧
    qR 1641278451780291167220080819 1250000000000000000000000000 ≤ p.d1 ∧ p.d1 ≤ qR
      1641278451780291167220330819 1250000000000000000000000000 ∧
    qR (-105076534082910887440587258861) 200000000000000000000000000000 ≤ p.d2 ∧ p.d2 ≤ qR
      (-105076534082910887440547258861) 200000000000000000000000000000 ∧
    qR 2420644844145377502832171437 2000000000000000000000000000 ≤ p.e1 ∧ p.e1 ≤ qR
      2420644844145377502832571437 2000000000000000000000000000 ∧
    qR 2499999999999999999999 10000000000000000000000 ≤ p.e2 ∧ p.e2 ≤ qR 2500000000000000000001
      10000000000000000000000 ∧
    qR 1958868239504182093160893749 50000000000000000000000000000 ≤ p.phi ∧ p.phi ≤ qR
      78354729580167283726435751 2000000000000000000000000000 ∧
    qR 34065075469136244723692787727 50000000000000000000000000000 ≤ p.theta ∧ p.theta ≤ qR
      34065075469136244723692787983 50000000000000000000000000000}

end Romik
end GerverSofa

namespace GerverSofa.Romik

/-- Every point in the certified direct-system box has a positive first
switching angle. -/
theorem phi_pos_of_mem_box {p : Params} (hp : p ∈ box) : 0 < p.phi := by
  dsimp [box, qR] at hp
  have hlo :
      ((1958868239504182093160893749 : ℝ) /
        50000000000000000000000000000) ≤ p.phi := by
    aesop
  have hpositive :
      (0 : ℝ) <
        ((1958868239504182093160893749 : ℝ) /
          50000000000000000000000000000) := by
    norm_num
  exact lt_of_lt_of_le hpositive hlo

/-- Equations (32)--(34), together with the certified box, force the exact
initial path normalisation `x(0)=(0,0)`. -/
theorem path_zero_of_mem_box_and_equations
    {p : Params} (hp : p ∈ box) (heq : Equations p) :
    path p 0 = (0, 0) := by
  have hphi : 0 < p.phi := phi_pos_of_mem_box hp
  have h5 := congrFun heq (5 : Fin 22)
  have h6 := congrFun heq (6 : Fin 22)
  have h7 := congrFun heq (7 : Fin 22)
  simp [system] at h5 h6 h7
  have h0phi : (0 : ℝ) ≤ p.phi := le_of_lt hphi
  apply Prod.ext <;>
    simp [path, h0phi, path1, rot, addK] <;>
    linarith

end GerverSofa.Romik

namespace GerverSofa.Romik

/-- The exact direct-system box orders the four physical switching times. -/
theorem switchOrder_of_mem_box {p : Params} (hp : p ∈ box) : SwitchOrder p := by
  dsimp [box, qR] at hp
  have hphiLo :
      ((1958868239504182093160893749 : ℝ) /
        50000000000000000000000000000) ≤ p.phi := by
    aesop
  have hphiHi :
      p.phi ≤ ((78354729580167283726435751 : ℝ) /
        2000000000000000000000000000) := by
    aesop
  have hthetaLo :
      ((34065075469136244723692787727 : ℝ) /
        50000000000000000000000000000) ≤ p.theta := by
    aesop
  have hthetaHi :
      p.theta ≤ ((34065075469136244723692787983 : ℝ) /
        50000000000000000000000000000) := by
    aesop
  have hphiTheta : p.phi ≤ p.theta := by
    norm_num at hphiHi hthetaLo
    linarith
  have hthetaEta : p.theta ≤ Real.pi / 2 - p.theta := by
    norm_num at hthetaHi
    nlinarith [Real.pi_gt_three]
  exact
    { phi_le_theta := hphiTheta
      theta_le_eta := hthetaEta
      eta_le_tau := by linarith }

/-- The certified box and the positional equations discharge the path
continuity field needed by the moving-sofa assembly. -/
theorem continuous_path_of_mem_box_and_equations
    {p : Params} (hp : p ∈ box) (heq : Equations p) :
    Continuous (path p) :=
  continuous_path_of_order_and_equations (switchOrder_of_mem_box hp) heq

end GerverSofa.Romik

namespace GerverSofa.Romik

/-- The direct-system box supplies the strict lower bound on `a₁` used in the
area proposition. -/
theorem a1_lower_bound_of_mem_box {p : Params} (hp : p ∈ box) :
    ((2420644844145377502832171437 : ℝ) /
      2000000000000000000000000000) ≤ p.a1 := by
  dsimp [box, qR] at hp
  aesop

end GerverSofa.Romik

end

end

end

section

/-!
# Concrete Gerver cap, niche and fixed sofa

The definitions follow the manuscript literally.  This file also proves the
closedness part of the main topological certificate directly from the
half-plane definitions; it does not use the numerical certificate or Baek's
cap theory.
-/

@[expose] public section

noncomputable section

namespace GerverSofa

/-- Euclidean scalar product in the fixed coordinate representation. -/
def dot (p q : Point) : ℝ := p.1 * q.1 + p.2 * q.2

/-- Rotating outer-wall normals. -/
def u (t : ℝ) : Point := (Real.cos t, Real.sin t)
/-- The vertical unit vector rotated counterclockwise through angle `t`. -/
def v (t : ℝ) : Point := (-Real.sin t, Real.cos t)

/-- The lower fan in the manuscript normalisation. -/
def capFan : Set Point := {q | 0 ≤ q.2}

/-- First rotating supporting half-plane. -/
def supportHalfU (p : Romik.Params) (t : ℝ) : Set Point :=
  {q | dot q (u t) ≤ dot (Romik.path p t) (u t) + 1}

/-- Second rotating supporting half-plane. -/
def supportHalfV (p : Romik.Params) (t : ℝ) : Set Point :=
  {q | dot q (v t) ≤ dot (Romik.path p t) (v t) + 1}

/-- The cap `K₀` reconstructed from the five-phase path. -/
def Romik.K0 (p : Romik.Params) : Set Point :=
  {q | 0 ≤ q.2 ∧
    ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      q ∈ supportHalfU p t ∩ supportHalfV p t}

/-- Open inner quadrant of the supporting hallway at physical angle `t`. -/
def Romik.innerQuadrantAt (p : Romik.Params) (t : ℝ) : Set Point :=
  let x := Romik.path p t
  {q | dot (q.1 - x.1, q.2 - x.2) (u t) < 0 ∧
       dot (q.1 - x.1, q.2 - x.2) (v t) < 0}

/-- Union of all forbidden inner quadrants at interior rotation times. -/
def Romik.innerUnion (p : Romik.Params) : Set Point :=
  {q | ∃ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), q ∈ Romik.innerQuadrantAt p t}

/-- The niche removed from the cap. -/
def Romik.niche (p : Romik.Params) : Set Point :=
  capFan ∩ Romik.innerUnion p

/-- The fixed Gerver candidate `G = K₀ \ N(K₀)`. -/
def Romik.sofa (p : Romik.Params) : Set Point :=
  Romik.K0 p \ Romik.niche p

/-- Physical supporting hallway at normalized time `s`. -/
def Romik.hallwayAt (p : Romik.Params) (s : ℝ) : Set Point :=
  supportingHallway (Romik.frame p s)

/-! ## Closedness facts independent of the numerical certificate -/

private theorem continuous_dot_fixed (a : Point) :
    Continuous (fun q : Point => dot q a) := by
  unfold dot
  fun_prop

private theorem continuous_shifted_dot (x a : Point) :
    Continuous (fun q : Point => dot (q.1 - x.1, q.2 - x.2) a) := by
  unfold dot
  fun_prop

/-- A fixed supporting half-plane is closed. -/
theorem isClosed_supportHalfU (p : Romik.Params) (t : ℝ) :
    IsClosed (supportHalfU p t) := by
  change IsClosed ((fun q : Point => dot q (u t)) ⁻¹'
    Set.Iic (dot (Romik.path p t) (u t) + 1))
  exact isClosed_Iic.preimage (continuous_dot_fixed (u t))

/-- The other fixed supporting half-plane is closed. -/
theorem isClosed_supportHalfV (p : Romik.Params) (t : ℝ) :
    IsClosed (supportHalfV p t) := by
  change IsClosed ((fun q : Point => dot q (v t)) ⁻¹'
    Set.Iic (dot (Romik.path p t) (v t) + 1))
  exact isClosed_Iic.preimage (continuous_dot_fixed (v t))

/-- The fan constraint is closed. -/
theorem isClosed_capFan : IsClosed capFan := by
  change IsClosed ((fun q : Point => q.2) ⁻¹' Set.Ici 0)
  exact isClosed_Ici.preimage continuous_snd

/-- The bounded-quantifier definition of `K₀` as an explicit intersection. -/
theorem Romik.K0_eq_inter_iInter (p : Romik.Params) :
    Romik.K0 p = capFan ∩
      ⋂ t : {t : ℝ // t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)},
        (supportHalfU p t.1 ∩ supportHalfV p t.1) := by
  ext q
  constructor
  · rintro ⟨hbase, hall⟩
    refine ⟨hbase, Set.mem_iInter.mpr ?_⟩
    intro t
    exact hall t.1 t.2
  · rintro ⟨hbase, hall⟩
    refine ⟨hbase, ?_⟩
    intro t ht
    exact Set.mem_iInter.mp hall ⟨t, ht⟩

/-- `K₀` is closed, before any support-maximisation or compactness argument. -/
theorem Romik.isClosed_K0 (p : Romik.Params) : IsClosed (Romik.K0 p) := by
  rw [Romik.K0_eq_inter_iInter]
  exact isClosed_capFan.inter <|
    isClosed_iInter fun t =>
      (isClosed_supportHalfU p t.1).inter (isClosed_supportHalfV p t.1)

/-- Every instantaneous inner quadrant is open. -/
theorem Romik.isOpen_innerQuadrantAt (p : Romik.Params) (t : ℝ) :
    IsOpen (Romik.innerQuadrantAt p t) := by
  let x := Romik.path p t
  have hu : IsOpen
      ((fun q : Point => dot (q.1 - x.1, q.2 - x.2) (u t)) ⁻¹' Set.Iio 0) :=
    isOpen_Iio.preimage (continuous_shifted_dot x (u t))
  have hv : IsOpen
      ((fun q : Point => dot (q.1 - x.1, q.2 - x.2) (v t)) ⁻¹' Set.Iio 0) :=
    isOpen_Iio.preimage (continuous_shifted_dot x (v t))
  change IsOpen
    (((fun q : Point => dot (q.1 - x.1, q.2 - x.2) (u t)) ⁻¹' Set.Iio 0) ∩
     ((fun q : Point => dot (q.1 - x.1, q.2 - x.2) (v t)) ⁻¹' Set.Iio 0))
  exact hu.inter hv

/-- The union of all interior-time inner quadrants is open. -/
theorem Romik.isOpen_innerUnion (p : Romik.Params) :
    IsOpen (Romik.innerUnion p) := by
  have hrepr : Romik.innerUnion p =
      ⋃ t : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)},
        Romik.innerQuadrantAt p t.1 := by
    ext q
    constructor
    · rintro ⟨t, ht, hq⟩
      exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, hq⟩
    · intro hq
      rcases Set.mem_iUnion.mp hq with ⟨t, hq⟩
      exact ⟨t.1, t.2, hq⟩
  rw [hrepr]
  exact isOpen_iUnion fun t => Romik.isOpen_innerQuadrantAt p t.1

/-- The cap lies in its fan by definition. -/
theorem Romik.K0_subset_capFan (p : Romik.Params) : Romik.K0 p ⊆ capFan := by
  intro q hq
  exact hq.1

/-- Since `K₀ ⊆ capFan`, removing the niche is the same as removing the open
union of forbidden quadrants. -/
theorem Romik.sofa_eq_K0_diff_innerUnion (p : Romik.Params) :
    Romik.sofa p = Romik.K0 p \ Romik.innerUnion p := by
  ext q
  constructor
  · rintro ⟨hqK, hqN⟩
    refine ⟨hqK, ?_⟩
    intro hqU
    exact hqN ⟨Romik.K0_subset_capFan p hqK, hqU⟩
  · rintro ⟨hqK, hqU⟩
    refine ⟨hqK, ?_⟩
    rintro ⟨_hqFan, hqInner⟩
    exact hqU hqInner

/-- The concrete fixed sofa candidate is closed for every parameter vector. -/
theorem Romik.isClosed_sofa (p : Romik.Params) : IsClosed (Romik.sofa p) := by
  rw [Romik.sofa_eq_K0_diff_innerUnion]
  simpa [Set.sdiff_eq] using
    (Romik.isClosed_K0 p).inter (Romik.isOpen_innerUnion p).isClosed_compl

end GerverSofa

namespace GerverSofa

/-! ## Algebraic hallway characterisation and endpoint assembly -/

@[simp] theorem Romik.mem_supportHalfU (p : Romik.Params) (t : ℝ) (q : Point) :
    q ∈ supportHalfU p t ↔
      dot q (u t) ≤ dot (Romik.path p t) (u t) + 1 := Iff.rfl

@[simp] theorem Romik.mem_supportHalfV (p : Romik.Params) (t : ℝ) (q : Point) :
    q ∈ supportHalfV p t ↔
      dot q (v t) ≤ dot (Romik.path p t) (v t) + 1 := Iff.rfl

@[simp] theorem Romik.mem_K0 (p : Romik.Params) (q : Point) :
    q ∈ Romik.K0 p ↔
      0 ≤ q.2 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        q ∈ supportHalfU p t ∩ supportHalfV p t := Iff.rfl

@[simp] theorem Romik.mem_innerUnion (p : Romik.Params) (q : Point) :
    q ∈ Romik.innerUnion p ↔
      ∃ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        q ∈ Romik.innerQuadrantAt p t := Iff.rfl

@[simp] theorem Romik.mem_niche (p : Romik.Params) (q : Point) :
    q ∈ Romik.niche p ↔ q ∈ capFan ∧ q ∈ Romik.innerUnion p := Iff.rfl

@[simp] theorem Romik.mem_sofa (p : Romik.Params) (q : Point) :
    q ∈ Romik.sofa p ↔ q ∈ Romik.K0 p ∧ q ∉ Romik.niche p := Iff.rfl

/-- The inverse supporting frame has exactly the two signed wall coordinates
used in the manuscript. -/
theorem Romik.frame_inv_act_formula (p : Romik.Params) (s : ℝ) (q : Point) :
    (Romik.frame p s).inv.act q =
      (dot (q.1 - (Romik.path p (Romik.angle s)).1,
            q.2 - (Romik.path p (Romik.angle s)).2) (u (Romik.angle s)),
       dot (q.1 - (Romik.path p (Romik.angle s)).1,
            q.2 - (Romik.path p (Romik.angle s)).2) (v (Romik.angle s))) := by
  apply Prod.ext <;>
    simp [Romik.frame, SE2.inv, SE2.act, dot, u, v] <;> ring

/-- A point is in the supporting hallway iff its two wall coordinates lie in
`Q⁺` but not simultaneously in the open inner quadrant `Q⁻`. -/
theorem Romik.mem_hallwayAt_iff_wall_coordinates
    (p : Romik.Params) (s : ℝ) (q : Point) :
    q ∈ Romik.hallwayAt p s ↔
      let t := Romik.angle s
      let x := Romik.path p t
      (dot (q.1 - x.1, q.2 - x.2) (u t) ≤ 1 ∧
       dot (q.1 - x.1, q.2 - x.2) (v t) ≤ 1) ∧
      ¬ (dot (q.1 - x.1, q.2 - x.2) (u t) < 0 ∧
         dot (q.1 - x.1, q.2 - x.2) (v t) < 0) := by
  rw [Romik.hallwayAt, mem_supportingHallway_iff]
  rw [Romik.frame_inv_act_formula]
  rw [hallway_eq_outer_diff_inner]
  simp [outerQuarter, innerQuarter]

/-- A sofa point cannot lie in an instantaneous forbidden quadrant at an
interior physical time. -/
theorem Romik.not_mem_innerQuadrantAt_of_mem_sofa
    (p : Romik.Params) {q : Point} (hq : q ∈ Romik.sofa p)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    q ∉ Romik.innerQuadrantAt p t := by
  intro hinner
  exact hq.2 ⟨Romik.K0_subset_capFan p hq.1, ⟨t, ht, hinner⟩⟩

/-- The lower-fan constraint excludes the initial inner quadrant once the
physical path starts at the origin. -/
theorem Romik.not_mem_initial_innerQuadrant
    (p : Romik.Params) (hzero : Romik.path p 0 = (0, 0))
    {q : Point} (hq : q ∈ Romik.sofa p) :
    q ∉ Romik.innerQuadrantAt p 0 := by
  intro hinner
  have hbase : 0 ≤ q.2 := hq.1.1
  have hneg : q.2 < 0 := by
    simpa [Romik.innerQuadrantAt, dot, u, v, hzero] using hinner.2
  exact (not_lt_of_ge hbase) hneg

/-- The lower-fan constraint excludes the final inner quadrant once the final
path point has second coordinate zero. -/
theorem Romik.not_mem_final_innerQuadrant
    (p : Romik.Params)
    (hend : (Romik.path p (Real.pi / 2)).2 = 0)
    {q : Point} (hq : q ∈ Romik.sofa p) :
    q ∉ Romik.innerQuadrantAt p (Real.pi / 2) := by
  intro hinner
  have hbase : 0 ≤ q.2 := hq.1.1
  have hneg : q.2 < 0 := by
    simpa [Romik.innerQuadrantAt, dot, u, v, hend] using hinner.1
  exact (not_lt_of_ge hbase) hneg

/-- The concrete cap-minus-niche set lies in every supporting hallway.  The
only endpoint input is the pair of path normalisations used in the paper. -/
theorem Romik.sofa_subset_hallwayAt
    (p : Romik.Params)
    (hzero : Romik.path p 0 = (0, 0))
    (hend : (Romik.path p (Real.pi / 2)).2 = 0) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1,
      Romik.sofa p ⊆ Romik.hallwayAt p s := by
  intro s hs q hq
  rw [Romik.mem_hallwayAt_iff_wall_coordinates]
  dsimp only
  have hangle : Romik.angle s ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    constructor
    · exact mul_nonneg hs.1 (by positivity)
    · have hm := mul_le_mul_of_nonneg_right hs.2
          (show 0 ≤ Real.pi / 2 by positivity)
      simpa [Romik.angle] using hm
  have hsupports := hq.1.2 (Romik.angle s) hangle
  constructor
  · constructor
    · have hu := hsupports.1
      change dot q (u (Romik.angle s)) ≤
        dot (Romik.path p (Romik.angle s)) (u (Romik.angle s)) + 1 at hu
      dsimp [dot] at hu ⊢
      linarith
    · have hv := hsupports.2
      change dot q (v (Romik.angle s)) ≤
        dot (Romik.path p (Romik.angle s)) (v (Romik.angle s)) + 1 at hv
      dsimp [dot] at hv ⊢
      linarith
  · change q ∉ Romik.innerQuadrantAt p (Romik.angle s)
    by_cases hs0 : s = 0
    · subst s
      simpa using Romik.not_mem_initial_innerQuadrant p hzero hq
    by_cases hs1 : s = 1
    · subst s
      simpa using Romik.not_mem_final_innerQuadrant p hend hq
    · have hsIoo : s ∈ Set.Ioo (0 : ℝ) 1 := by
        exact ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0),
          lt_of_le_of_ne hs.2 hs1⟩
      have hangleIoo : Romik.angle s ∈
          Set.Ioo (0 : ℝ) (Real.pi / 2) := by
        constructor
        · exact mul_pos hsIoo.1 (by positivity)
        · have hm := mul_lt_mul_of_pos_right hsIoo.2
              (show 0 < Real.pi / 2 by positivity)
          simpa [Romik.angle] using hm
      exact Romik.not_mem_innerQuadrantAt_of_mem_sofa p hq hangleIoo

/-- The inverse frame at time zero places the concrete sofa in the horizontal
arm. -/
theorem Romik.initial_arm_of_path_zero
    (p : Romik.Params) (hzero : Romik.path p 0 = (0, 0)) :
    ((Romik.frame p 0).inv.act '' Romik.sofa p) ⊆ horizontalArm := by
  rintro y ⟨q, hq, rfl⟩
  have htime : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    constructor <;> positivity
  have hs := hq.1.2 0 htime
  have hx : q.1 ≤ 1 := by
    have hu := hs.1
    simpa [supportHalfU, dot, u, hzero] using hu
  have hy0 : 0 ≤ q.2 := hq.1.1
  have hy1 : q.2 ≤ 1 := by
    have hv := hs.2
    simpa [supportHalfV, dot, v, hzero] using hv
  rw [Romik.frame_inv_act_formula]
  simpa [Romik.angle, hzero, dot, u, v, horizontalArm] using
    (show q.1 ≤ 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1 from ⟨hx, hy0, hy1⟩)

/-- The inverse frame at time one places the concrete sofa in the vertical
arm. -/
theorem Romik.final_arm_of_path_end_y_zero
    (p : Romik.Params)
    (hend : (Romik.path p (Real.pi / 2)).2 = 0) :
    ((Romik.frame p 1).inv.act '' Romik.sofa p) ⊆ verticalArm := by
  rintro y ⟨q, hq, rfl⟩
  have htime : Real.pi / 2 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    constructor
    · positivity
    · rfl
  have hs := hq.1.2 (Real.pi / 2) htime
  have hy0 : 0 ≤ q.2 := hq.1.1
  have hy1 : q.2 ≤ 1 := by
    have hu := hs.1
    simpa [supportHalfU, dot, u, hend] using hu
  have hv := hs.2
  have hv1 :
      dot (q.1 - (Romik.path p (Real.pi / 2)).1,
           q.2 - (Romik.path p (Real.pi / 2)).2) (v (Real.pi / 2)) ≤ 1 := by
    change dot q (v (Real.pi / 2)) ≤
      dot (Romik.path p (Real.pi / 2)) (v (Real.pi / 2)) + 1 at hv
    dsimp [dot] at hv ⊢
    linarith
  rw [Romik.frame_inv_act_formula]
  simpa [Romik.angle, dot, u, v, hend, verticalArm] using
    (show 0 ≤ q.2 ∧ q.2 ≤ 1 ∧
      dot (q.1 - (Romik.path p (Real.pi / 2)).1,
           q.2 - (Romik.path p (Real.pi / 2)).2) (v (Real.pi / 2)) ≤ 1
      from ⟨hy0, hy1, hv1⟩)

end GerverSofa

end

end

end
