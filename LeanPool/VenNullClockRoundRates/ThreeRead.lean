/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

module

public import LeanPool.VenNullClockRoundRates.ThreeReadModel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! The positive three-read theorem, with the angular coefficient obtained by
polarizing the even marginal projection moments. No signed contrast, axis
overlap formula, or desired separating inequality is assumed. -/
public section
noncomputable section
open MeasureTheory
namespace VenSplit
variable {Ω : Type*} [MeasurableSpace Ω]

private inductive D | two | three | four
private def D.k : D → ℕ | .two => 2 | .three => 3 | .four => 4
private structure T where
  wt : ℝ
  u : ℝ
  v : ℝ
  d : D

private def val (p : T) (a b : ℝ) : ℝ := p.wt * (p.u*a+p.v*b)^(2*p.d.k)
private def avg (p : T) (c : ℝ) : ℝ :=
  p.wt * ((p.u^2+2*p.u*p.v*c+p.v^2)^p.d.k/(2*(p.d.k:ℝ)+1))
private def vals : List T → ℝ → ℝ → ℝ
 | [], _, _ => 0 | p::ps, a,b => val p a b + vals ps a b
private def avgs : List T → ℝ → ℝ
 | [], _ => 0 | p::ps,c => avg p c + avgs ps c
/-- A polarization stencil for the squared difference of quartic energies. -/
private def stencil : List T := [
 ⟨16/3,1,0,.two⟩, ⟨16/3,0,1,.two⟩, ⟨-2/3,1,1,.two⟩, ⟨-2/3,1,-1,.two⟩,
 ⟨-64/15,1,0,.three⟩, ⟨-64/15,0,1,.three⟩, ⟨2/15,1,1,.three⟩, ⟨2/15,1,-1,.three⟩,
 ⟨17/20,1,0,.four⟩, ⟨17/20,0,1,.four⟩, ⟨-17/630,1,1,.four⟩, ⟨-17/630,1,-1,.four⟩,
 ⟨1/2520,2,1,.four⟩, ⟨1/2520,2,-1,.four⟩, ⟨1/2520,1,2,.four⟩, ⟨1/2520,1,-2,.four⟩]

private theorem stencil_point (a b : ℝ) : (energy a - energy b)^2 = vals stencil a b := by
  simp only [stencil, vals, val, D.k, energy]
  ring

private theorem stencil_avg (c : ℝ) : avgs stencil c = (16/315)*(1-c ^ 2)*(7+c ^ 2) := by
  simp only [stencil, avgs, avg, D.k, Nat.cast_ofNat]
  ring

private theorem integrate_stencil {μ : Measure Ω} {A B : Ω → ℝ} {c : ℝ}
    (h : AxisProjectionLaw μ A B c) (ps : List T) :
    Integrable (fun y ↦ vals ps (A y) (B y)) μ ∧
    (∫ y, vals ps (A y) (B y) ∂μ) = avgs ps c := by
  induction ps with
  | nil => simp [vals, avgs]
  | cons p ps ih =>
    have hlo : 2 ≤ p.d.k := by cases p.d <;> decide
    have hhi : p.d.k ≤ 4 := by cases p.d <;> decide
    obtain ⟨hi,he⟩ := h p.u p.v p.d.k hlo hhi
    have hiv : Integrable (fun y ↦ val p (A y) (B y)) μ := hi.const_mul p.wt
    refine ⟨hiv.add ih.1, ?_⟩
    change (∫ y, val p (A y) (B y) + vals ps (A y) (B y) ∂μ) = avg p c + avgs ps c
    rw [integral_add hiv ih.1, ih.2]
    simp only [val, integral_const_mul, he, avg]

/-- Exact unweighted mismatch from ordinary one-direction spherical moments. -/
theorem angular_mismatch {μ : Measure Ω} {A B : Ω → ℝ} {c : ℝ}
    (h : AxisProjectionLaw μ A B c) :
    Integrable (fun y ↦ (energy (A y) - energy (B y))^2) μ ∧
    (∫ y, (energy (A y) - energy (B y))^2 ∂μ) = (16/315)*(1-c ^ 2)*(7+c ^ 2) := by
  simpa only [stencil_point, stencil_avg] using integrate_stencil h stencil

private theorem exp_gap {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) :
    a-b ≤ Real.exp a - Real.exp b := by
  have hp := Real.add_one_le_exp (a-b)
  have he := Real.one_le_exp hb
  have hg := mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hab)
  have hm := mul_le_mul_of_nonneg_left hp (Real.exp_pos b).le
  have hx : Real.exp b * Real.exp (a-b) = Real.exp a := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hx] at hm
  linarith

private theorem exp_gap_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a-b)^2 ≤ (Real.exp a - Real.exp b)^2 := by
  rcases le_total b a with h|h
  · have p := exp_gap hb h
    have q := sq_le_sq' (by linarith : -(Real.exp a - Real.exp b) ≤ a-b) p
    exact q
  · have p := exp_gap ha h
    have q := sq_le_sq' (by linarith : -(Real.exp b - Real.exp a) ≤ b-a) p
    nlinarith

private def quad (A B w : Ω → ℝ) (t : ℝ) (y : Ω) : ℝ :=
  w y * (Real.exp (t*energy (A y)) - Real.exp (t*energy (B y)))^2

omit [MeasurableSpace Ω] in
private theorem point_split (A B w : Ω → ℝ) (t : ℝ) (y : Ω) :
    quad A B w t y = ray A B w (2*t) 0 y - 2*ray A B w t t y + ray A B w 0 (2*t) y := by
  simp only [quad, ray, zero_mul, add_zero, zero_add]
  have hh (e : ℝ) : Real.exp (2*t*e) = Real.exp (t*e)*Real.exp (t*e) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hh,hh,Real.exp_add]
  ring

private theorem integral_split {μ : Measure Ω} {A B w : Ω → ℝ} {t : ℝ}
    (hI : ThreeIntegrable μ A B w t) :
    Integrable (quad A B w t) μ ∧ (∫ y, quad A B w t y ∂μ) = split μ A B w t := by
  obtain ⟨h0,hm,h2⟩ := hI
  have hx : Integrable (fun y ↦ ray A B w (2*t) 0 y - 2*ray A B w t t y) μ :=
    h0.sub (hm.const_mul 2)
  have hpt : quad A B w t = fun y ↦ ray A B w (2*t) 0 y - 2*ray A B w t t y + ray A B w 0 (2*t) y :=
    funext (point_split A B w t)
  rw [hpt]
  exact ⟨hx.add h2, by
    rw [integral_add hx h2, integral_sub h0 (hm.const_mul 2), integral_const_mul]
    rfl⟩

omit [MeasurableSpace Ω] in
private theorem ray_lower {A B w : Ω → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hw : ∀ y, 1 ≤ w y) (y : Ω) :
    t^2*(energy (A y) - energy (B y))^2 ≤ quad A B w t y := by
  have ha : 0 ≤ energy (A y) := sq_nonneg _
  have hb : 0 ≤ energy (B y) := sq_nonneg _
  have h1 := exp_gap_sq (mul_nonneg ht ha) (mul_nonneg ht hb)
  have h2 := mul_nonneg (sub_nonneg.mpr (hw y))
    (sq_nonneg (Real.exp (t*energy (A y))-Real.exp (t*energy (B y))))
  dsimp [quad]; nlinarith

theorem split_lower_bound {μ : Measure Ω} {A B w : Ω → ℝ} {c t : ℝ}
    (h : AxisProjectionLaw μ A B c) (ht : 0 ≤ t) (hw : ∀ y, 1 ≤ w y)
    (hI : ThreeIntegrable μ A B w t) : margin t c ≤ split μ A B w t := by
  obtain ⟨hL,hv⟩ := angular_mismatch h
  obtain ⟨hQ,hq⟩ := integral_split hI
  have hp := integral_mono (hL.const_mul (t^2)) hQ (ray_lower ht hw)
  rw [integral_const_mul, hv, hq] at hp
  change (16*t^2/315)*(1-c ^ 2)*(7+c ^ 2) ≤ _
  linarith

private theorem aligned_zero {μ : Measure Ω} {A B w : Ω → ℝ} {c t : ℝ}
    (h : AxisProjectionLaw μ A B c) (hal : c ^ 2 = 1)
    (hI : ThreeIntegrable μ A B w t) : split μ A B w t = 0 := by
  obtain ⟨hL,hv⟩ := angular_mismatch h
  rw [hal] at hv
  have hz : (∫ y, (energy (A y)-energy (B y))^2 ∂μ) = 0 := by linarith
  have he := (integral_eq_zero_iff_of_nonneg (fun _ ↦ sq_nonneg _) hL).mp hz
  rw [← (integral_split hI).2]
  calc
    _ = ∫ _, (0:ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [he] with y hy
      have heq : energy (A y)=energy (B y) := by
        change (energy (A y)-energy (B y))^2=0 at hy
        nlinarith [sq_nonneg (energy (A y)-energy (B y))]
      simp [quad, heq]
    _ = _ := by simp

/-- Deterministic control of the signed-contrast error, including correlated errors. -/
theorem reading_error {hi mid lo x y z ε : ℝ}
    (hx : |hi - x| ≤ ε) (hy : |mid - y| ≤ ε) (hz : |lo - z| ≤ ε) :
    |contrast hi mid lo - contrast x y z| ≤ 4*ε := by
  rw [abs_le] at *
  dsimp [contrast]; constructor <;> linarith [hx.1,hx.2,hy.1,hy.2,hz.1,hz.2]

/-- Three calibrated exponential readings: separation at the explicit uniform
angular margin, exact alignment equivalence, and a worst-case absolute-noise test. -/
theorem split_certificate : SplitCertificate := by
  intro Ω _ μ _ A B w c t h hc ht hw hI
  have hlow := split_lower_bound h ht.le hw hI
  have eqv : split μ A B w t = 0 ↔ c ^ 2=1 := by
    refine ⟨?_,fun hal ↦ aligned_zero h hal hI⟩
    intro hz
    by_contra hn
    have hlt := lt_of_le_of_ne hc hn
    have hm : 0 < margin t c := by
      dsimp [margin]; exact mul_pos (mul_pos (by positivity) (sub_pos.mpr hlt)) (by positivity)
    linarith
  refine ⟨hlow,eqv,?_⟩
  intro hi mid lo ε hhi hmid hlo
  have err := reading_error hhi hmid hlo
  change |contrast hi mid lo - split μ A B w t| ≤ 4*ε at err
  rw [abs_le] at err
  constructor
  · intro hgt hal
    have hz := eqv.mpr hal
    linarith [err.2]
  · intro hm
    linarith [err.1]

/-- The three calibrated reads give the weighted exponential square. -/
theorem split_integral {μ : Measure Ω} {A B w : Ω → ℝ} {t : ℝ}
    (hI : ThreeIntegrable μ A B w t) :
    split μ A B w t =
      ∫ y, w y * (Real.exp (t * energy (A y)) - Real.exp (t * energy (B y))) ^ 2 ∂μ := by
  exact (integral_split hI).2.symm

end VenSplit
end
