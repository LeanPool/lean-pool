/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.General.Weight
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Proof.Accept
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Geometry.Decoding
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.General.Scales
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Waves.Scenario
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Assembly.Prepare.Status

/-! # Per-cell credit certificates for every term of the expansion -/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input
open Assembly Coloring Routing.Private Sphere SphereScale Surface Surface.Local Finset Transcript

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} (sc : Scales g ℓ D T (p ^ l) b d) {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}
    (h : P.ReadyPanel A hK hF mobility k U status pres)

local notation "Cfg" => design S g ℓ D b d p l

local notation "H" => SphereScale.energy ℓ D (d * b)

open scoped Classical in
/-- Computes the credit by the application `credits S hK hF mobility k ((((q.code i).tape
(A.coord v).1).2 (A.coord v).2))`. -/
abbrev ReadyPanel.credit (s : P.InitialShapes ℓ) (q : h.Motion sc s) (i : q.I) (v : P.Occupied) :=
  credits S hK hF mobility k ((((q.code i).tape (A.coord v).1).2 (A.coord v).2))

open scoped Classical in
/-- The construction uses `q.code i` for its intermediate `c`. -/
def ReadyPanel.measuredCode (s : P.InitialShapes ℓ) (q : h.Motion sc s) (i : q.I) :
    U.MeasuredRelease pres (q.code i).tape status
      ((P.localWorld A sc hK s).eval (q.code i).frame) ℓ A.coord (h.credit sc s q i) := by
  let c := q.code i
  let init := P.plant (P.kit sc hK) s
  let E v := Geometry.clip (Cfg).waves (p ^ l * H) (init.energyCre (p ^ l) H (2 * g) v)
  let M v := init.timeCre (p ^ l) H (D ^ 5) v
  have last := (P.check_motion A sc hK s q i (E := E) (M := M) (fun _ => ⟨le_rfl, le_rfl⟩)).2
  have sig := P.printSignal A sc hK s pres h.placed h.directed c U h.first h.second h.menu
    status h.location h.parents
  have bd := P.panelBounds A sc hK s c.frame
  have keep := P.namedKeeps (P.kit sc hK) s c.frame.reach h.placed c.frame.match'
  refine sig.1.measuredRelease keep h.populated bd sc h.first h.second rfl rfl rfl rfl h.units
    h.cap h.digits
    h.directed (h.credit sc s q i) ?_ ?_
  · intro v
    exact (c.frame.stage.collectors_timeCre (p ^ l) H (D ^ 5) v).trans_eq (last v).2.symm
  · intro v
    exact (Geometry.clip_mono (Cfg).waves (p ^ l * H)
      (c.frame.stage.collected_energyCre (p ^ l) H (2 * g) v)).trans_eq (last v).1.symm

open scoped Classical in
/-- The measured used in the `Input` construction. -/
structure Measured extends Expansion sc h where
  checked : ∀ i : toExpansion.I, U.Checked pres ℓ A.coord (h.credit sc i.1 (motion i.1) i.2.1)
    (toExpansion.record i) (toExpansion.term i) (toExpansion.shows i)

open scoped Classical in
/-- The measured of type `Measured sc h`, constructed using `(h.expand sc).motion`. -/
def ReadyPanel.measured : Measured sc h := by
  let motion := (h.expand sc).motion
  let out s i := h.measuredCode sc s (motion s) i
  exact { motion := motion
          release := fun s i => (out s i).toNamedRelease
          checked := fun i => (out i.1 i.2.1).checked i.2.2 }

end MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input
end

/-
# Constants for one controlled expansion

Only the width of the neighbor index affects the sizes of the
colorings and local lookups. This width ranges over a fixed finite
set, independently of the number of hosts and blocks.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.SphereScale
open Assembly Sphere Surface.Local

/-- The quantity computed by `(4 * 5) ^ 300`. -/
abbrev groupedDegree := (4 * 5) ^ 300
/-- Computes the allot by the application `Layout.Sharing.allocation groupedDegree 10`. -/
abbrev allot := Layout.Sharing.allocation groupedDegree 10
/-- The quantity computed by `s.C * s.D * s.M`. -/
def cap (s : Plan) := s.C * s.D * s.M

/-- The quantity computed by `(2 * A + 2) * ((D ^ 5 + 1) * (M + 1))`. -/
def slope (A D M : ℕ) := (2 * A + 2) * ((D ^ 5 + 1) * (M + 1))

theorem selector_width (A D M T Q f : ℕ) (hT : T ≤ 2 ^ f) (hQ : Q ≤ 2 ^ f) :
    selectorBits A D M T Q ≤ slope A D M * (1 + f) := by
  have h (X : ℕ) (hx : X ≤ 2 ^ f) : Nat.clog 2 (X + 1) ≤ f + 1 := by
    apply (Nat.clog_le_iff_le_pow (by decide)).mpr
    rw [pow_succ]
    have := Nat.two_pow_pos f
    omega
  unfold selectorBits slope
  rw [mul_right_comm (2 * A + 2)]
  apply Nat.mul_le_mul_right
  refine (Nat.add_le_add (Nat.mul_le_mul_left A (Nat.add_le_add_left (h _ hT) _))
    (Nat.mul_le_mul_right 2 (h _ hQ))).trans ?_
  ring_nf
  omega

/-- Constant multipliers for the two dictionaries. -/
structure Reserve where
  /-- Stores the deg associated with this `Reserve`. -/
  deg : ℕ
  /-- The number of transitions. -/
  steps : ℕ
  /-- Stores the waves associated with this `Reserve`. -/
  waves : ℕ
  /-- Stores the inflation associated with this `Reserve`. -/
  inflation : ℕ
  /-- Stores the slope associated with this `Reserve`. -/
  slope : ℕ
  /-- Stores the digits associated with this `Reserve`. -/
  digits : ℕ
  /-- Stores the child associated with this `Reserve`. -/
  child : ℕ
  /-- Stores the span associated with this `Reserve`. -/
  span : ℕ

namespace Reserve
variable (r : Reserve)

/-- The quantity computed by `r.inflation * (1 + r.slope)`. -/
def motion := r.inflation * (1 + r.slope)
/-- The quantity computed by `2 ^ (r.deg + 1) * (2 ^ (r.deg + 1) * (r.motion + r.digits))`. -/
def window := 2 ^ (r.deg + 1) * (2 ^ (r.deg + 1) * (r.motion + r.digits))
/-- The quantity computed by `r.window + r.child`. -/
def label := r.window + r.child
/-- Uses `Print.Children.degree r.deg r.child` as the representation. -/
def degree := Print.Children.degree r.deg r.child
/-- The value specified by `10001 + 2 ^ (r.deg + 1) + 2 ^ r.child + 2 ^ r.degree + 2 ^ (1 + 2 ^
r.deg + 12 * (2 ^ r.deg) ^ 3 + 2 ^ r.child)`. -/
def overhead := 10001 + 2 ^ (r.deg + 1) + 2 ^ r.child + 2 ^ r.degree + 2 ^ (1 + 2 ^ r.deg
    + 12 * (2 ^ r.deg) ^ 3 + 2 ^ r.child)
/-- The scale used in the `Reserve` construction. -/
def scale := r.overhead + 2 ^ r.span + 8 + 4 * r.waves + r.steps + 2 * r.child + r.motion
    + 2 * r.label +
  2 ^ r.child * r.label + 2 * r.span

end Reserve

/-- The reserve of type `Reserve`, constructed using `chunks 10 s.D`. -/
def reserve (s : Plan) (A : ℕ) (a : Sphere.Surface.Local.Design) : Reserve :=
  let M := chunks 10 s.D
  let slot := Print.Children.Part M s.D allot s.d
  let lane := Print.Compass.FinalLane (Fin a.R) (Input.panelKeys a) M s.D allot s.d
  ⟨a.d, a.hops, a.waves, a.inflation, slope A s.D a.M, M * (a.R + 2 * (2 * s.D ^ allot)),
    Print.indexBits slot, Print.indexBits (Print.Band lane (cap s))⟩

/-- Uses `⟨0, d, 0, 0, 0, 0, fun _ => ⟨fun _ _ => 0, fun _ _ => false, fun _ _ => none, fun _ _
=> 1⟩⟩` as the representation. -/
def skeleton (d : ℕ) : Scheme ℕ :=
  ⟨0, d, 0, 0, 0, 0, fun _ => ⟨fun _ _ => 0, fun _ _ => false, fun _ _ => none, fun _ _ => 1⟩⟩

/-- The value specified by `(reserve s A (Input.design (skeleton t) groupedDegree 10 s.D 0 0 0
0)).scale`. -/
def profile (s : Plan) (A t : ℕ) :=
  (reserve s A (Input.design (skeleton t) groupedDegree 10 s.D 0 0 0 0)).scale

private theorem fixedShape {F : Type} (S : Scheme F) (s : Plan) (A b d p l : ℕ) :
    (reserve s A (Input.design S groupedDegree 10 s.D b d p l)).scale = profile s A S.d := by
  unfold profile
  congr 1

/-- The quantity computed by `(Finset.range (s.D ^ 10 + 1)).sup (profile s A)`. -/
def upper (s : Plan) (A : ℕ) := (Finset.range (s.D ^ 10 + 1)).sup (profile s A)

theorem reserve_le {F : Type} (S : Scheme F) (s : Plan) (A b d p l : ℕ) (h : 2 ^ (S.d + 1)
    ≤ s.D ^ 10) :
    (reserve s A (Input.design S groupedDegree 10 s.D b d p l)).scale ≤ upper s A := by
  rw [fixedShape]
  have hh := (Nat.lt_two_pow_self (n := S.d + 1)).trans_le h
  exact Finset.le_sup (Finset.mem_range.mpr (by omega))

end MatrixMultiplicationAllFields.MatrixExponent.Rounds.SphereScale
end

/- # Linear bounds for the widths of the three control dictionaries -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.SphereScale.Reserve
variable (r : Reserve)

/-- The data for the fits construction, including `common`, `hops`, `child`, `parent`,
`contacts`. -/
structure Fits (J : ℕ) : Prop where
  common : 10001 + 4 * r.waves + 2 ^ r.deg ≤ J
  hops : r.steps ≤ J
  child : 2 * r.child + 2 ≤ J
  parent : 2 ^ r.deg ≤ J
  contacts : 2 ^ r.child ≤ J
  degree : 2 ^ r.degree ≤ J
  span : 2 ^ r.span ≤ J
  motion : r.motion ≤ J
  labels : r.motion + 2 * r.label ≤ J
  price : r.overhead + 2 * r.label ≤ J
  station : r.motion + 2 ^ r.child * r.label + 2 * r.span + 2 * r.child + 4 ≤ J

theorem fits {J : ℕ} (h : r.scale ≤ J) : r.Fits J := by
  have ht := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_succ r.deg)
  unfold scale overhead at h
  constructor <;> (try unfold overhead)
    <;> generalize 2 ^ (1 + 2 ^ r.deg + 12 * (2 ^ r.deg) ^ 3 + 2 ^ r.child) = c at *
    <;> generalize 2 ^ r.degree = y, 2 ^ r.span = x, 2 ^ r.child = t, 2 ^ (r.deg + 1) = i,
      2 ^ r.deg = j at *
    <;> omega

theorem motion_bound {k e f : ℕ} (hk : k ≤ r.slope * (1 + f)) :
    r.inflation * (1 + e + k) ≤ r.motion * (1 + e + f) := by
  rw [motion, mul_assoc]
  gcongr
  rw [add_mul, one_mul]
  have h := hk.trans (Nat.mul_le_mul_left _ (by omega : 1 + f ≤ 1 + e + f))
  omega

theorem window_bound {w x f : ℕ} (hw : w ≤ r.motion * x) (hf : f ≤ x) :
    2 ^ (r.deg + 1) * (2 ^ (r.deg + 1) * (w + f * r.digits)) ≤ r.window * x := by
  unfold window
  rw [mul_assoc, mul_assoc, add_mul, mul_comm f]
  gcongr

variable {J i j x h e w : ℕ}

theorem Fits.priced {r : Reserve} (hr : r.Fits J) (hx : 0 < x)
    (hi : i ≤ r.motion * x) (hj : j ≤ r.window * x) :
    i + 2 * (j + r.child) ≤ J * x ∧ r.overhead + j + (j + r.child) ≤ J * x := by
  have h₁ := Nat.le_mul_of_pos_right r.child hx
  have h₂ := Nat.le_mul_of_pos_right r.overhead hx
  have h₃ := Nat.mul_le_mul_right x hr.labels
  have h₄ := Nat.mul_le_mul_right x hr.price
  unfold label at h₃ h₄
  rw [add_mul, mul_assoc, add_mul] at h₃ h₄
  omega

theorem Fits.transferred {r : Reserve} (hr : r.Fits J) (hx : 0 < x)
    (hi : i ≤ r.motion * x) (hj : j ≤ r.window * x) :
    i + 2 ^ r.child * (j + r.child) + 2 * (h + (r.span + e)) + 1 + 2 * r.child + (w + 1) ≤ J * (x
      + h + e + w) := by
  have hc : j + r.child ≤ r.label * x := by
    unfold label
    rw [add_mul]
    exact Nat.add_le_add hj (Nat.le_mul_of_pos_right _ hx)
  have hm := Nat.mul_le_mul_left (2 ^ r.child) hc
  have he := Nat.le_mul_of_pos_right (2 * r.span + 2 * r.child + 4) hx
  have hd := Nat.mul_le_mul_right x hr.station
  have hh := Nat.mul_le_mul_right (h + e + w) (show 2 ≤ J by have := hr.child; omega)
  generalize 2 ^ r.child = c at *
  simp only [mul_add, add_mul, mul_assoc] at hm he hd hh ⊢
  omega

end MatrixMultiplicationAllFields.MatrixExponent.Rounds.SphereScale.Reserve
end
