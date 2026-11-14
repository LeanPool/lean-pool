/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Positivity
public import Mathlib.Topology.MetricSpace.Pseudo.Real

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.Complex.Module

-- [TABLET NODE: P4903T1SignedDiskHull]

/-!
# P4903T1SignedDiskHull

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4903T1SignedDiskHull (a b r D x tL B n : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hD : 0 < D)
    (hn : n * n = 1) (hDsq : D ^ 2 = 4 * a * b)
    (hx : r < x) (hy : r < D - x)
    (hmargin : D * a + (b - a) * x - D * r = r * (a + b) + a * b) :
    Metric.ball (⟨B-n*r,tL+x⟩ : ℂ) r ⊆
      convexHull ℝ (Set.range
        (![⟨B,tL⟩,⟨B-n*a,tL⟩,⟨B-n*b,tL+D⟩,⟨B,tL+D⟩] : Fin 4 → ℂ)) := by
-- BODY
  have cauchyBound : ∀ (a b r D n dx dy : ℝ), 0 < a → 0 < b → 0 < r →
      n*n=1 → D^2=4*a*b → dx^2+dy^2<r^2 →
      |D*n*dx+(b-a)*dy|<r*(a+b) := by
    intro a b r D n dx dy ha hb hr hn hD hdisc
    have hcoef : (D*n)^2+(b-a)^2=(a+b)^2 := by nlinarith [hn,hD]
    have hcs : (D*n*dx+(b-a)*dy)^2 ≤ (a+b)^2*(dx^2+dy^2) := by
      nlinarith [sq_nonneg (D*n*dy-(b-a)*dx), hcoef]
    have hab : 0<a+b := by linarith only [ha,hb]
    have hcoefpos : 0<(a+b)^2 := sq_pos_of_pos hab
    have hprod : (a+b)^2*(dx^2+dy^2)<(a+b)^2*r^2 :=
      mul_lt_mul_of_pos_left hdisc hcoefpos
    have hbound : (D*n*dx+(b-a)*dy)^2<(r*(a+b))^2 := by
      calc
        _ ≤ (a+b)^2*(dx^2+dy^2) := hcs
        _ < (a+b)^2*r^2 := hprod
        _ = (r*(a+b))^2 := by ring
    apply abs_lt.mpr
    constructor <;> nlinarith [hbound,mul_pos hr hab]
  intro z hz
  let c : ℂ := ⟨B-n*r,tL+x⟩
  let v : Fin 4 → ℂ :=
    ![⟨B,tL⟩,⟨B-n*a,tL⟩,⟨B-n*b,tL+D⟩,⟨B,tL+D⟩]
  let w : ℂ := z-c
  have hznorm : ‖w‖ < r := by simpa [w,c,dist_eq_norm] using hz
  have hnormNonneg : 0 ≤ ‖w‖ := Complex.norm_nonneg w
  have hsq : ‖w‖^2 < r^2 :=
    (sq_lt_sq₀ (M₀ := ℝ) (a := ‖w‖) (b := r)
      hnormNonneg hr.le).2 hznorm
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im] at hsq
  have hcoordsq : (z.re-c.re)^2+(z.im-c.im)^2<r^2 := by
    simpa only [pow_two] using hsq
  let X : ℝ := -n*(z.re-B)
  have hXrel : X-r=-n*(z.re-c.re) := by
    dsimp [X,c]
    nlinarith [hn]
  have hXsq : (X-r)^2<r^2 := by
    calc
      (X-r)^2 = (-n*(z.re-c.re))^2 := by rw [hXrel]
      _ = (z.re-c.re)^2 := by nlinarith [hn]
      _ < r^2 := lt_of_le_of_lt
        (le_add_of_nonneg_right (sq_nonneg (z.im-c.im))) hcoordsq
  have hXabs : |X-r|<r := by
    rw [abs_lt]
    constructor <;> nlinarith only [hXsq,hr]
  have hXpos : 0<X := by
    have hlow := (abs_lt.mp hXabs).1
    linarith only [hlow]
  have hYabs : |z.im-(tL+x)|<r := by
    have hh := (Complex.abs_im_le_norm w).trans_lt hznorm
    simpa [w,c,Complex.sub_im] using hh
  have hYlow : tL<z.im := by
    have hh := (abs_lt.mp hYabs).1
    linarith only [hh,hx]
  have hYhigh : z.im<tL+D := by
    have hh := (abs_lt.mp hYabs).2
    linarith only [hh,hy]
  let dx : ℝ := z.re-c.re
  let dy : ℝ := z.im-c.im
  have hdisc : dx^2+dy^2<r^2 := by simpa [dx,dy] using hcoordsq
  have hlin := cauchyBound a b r D n dx dy ha hb hr hn hDsq hdisc
  have htail := (abs_lt.mp hlin).1
  have hXeq : X-r=-n*dx := by simpa [dx] using hXrel
  have hcross : 0<D*a+(b-a)*(z.im-tL)-D*X := by
    have habpos : 0<a*b := mul_pos ha hb
    have hdy : dy=z.im-(tL+x) := by dsimp [dy,c]
    have hY : z.im-tL=x+dy := by rw [hdy]; ring
    have hXe : X=r-n*dx := by linarith only [hXeq]
    have hcrossEq : D*a+(b-a)*(z.im-tL)-D*X =
        (D*a+(b-a)*x-D*r)+(D*n*dx+(b-a)*dy) := by
      rw [hY,hXe]
      ring
    have hpos : 0<(D*a+(b-a)*x-D*r)+(D*n*dx+(b-a)*dy) := by
      rw [hmargin]
      linarith only [htail,habpos]
    rw [hcrossEq]
    exact hpos
  have hnum : D*X<(D-(z.im-tL))*a+(z.im-tL)*b := by
    nlinarith only [hcross]
  have hXtop : X<((tL+D-z.im)*a+(z.im-tL)*b)/D := by
    rw [lt_div_iff₀ hD]
    nlinarith only [hnum]
  let u : ℝ := (z.im-tL)/D
  let R : ℝ := (1-u)*a+u*b
  let theta : ℝ := X/R
  have hu0 : 0≤u := by dsimp [u]; positivity
  have hu1 : u≤1 := by
    dsimp [u]
    rw [div_le_one hD]
    linarith only [hYhigh]
  have hRpos : 0<R := by
    by_cases hu : u=0
    · simpa [R,hu] using ha
    · have hupos : 0<u := lt_of_le_of_ne hu0 (Ne.symm hu)
      dsimp [R]
      have hleft : 0≤(1-u)*a := mul_nonneg (sub_nonneg.mpr hu1) ha.le
      have hright : 0<u*b := mul_pos hupos hb
      linarith only [hleft,hright]
  have hReq : R=((tL+D-z.im)*a+(z.im-tL)*b)/D := by
    dsimp [R,u]
    field_simp [ne_of_gt hD]
    ring
  have hXleR : X≤R := by rw [hReq]; exact le_of_lt hXtop
  have htheta0 : 0≤theta := by dsimp [theta]; positivity
  have htheta1 : theta≤1 := by
    dsimp [theta]
    rw [div_le_one hRpos]
    exact hXleR
  have hzRe : z.re=B-n*X := by
    dsimp [X]
    calc
      z.re = B+(z.re-B) := by ring
      _ = B+(n*n)*(z.re-B) := by rw [hn]; ring
      _ = B-n*(-n*(z.re-B)) := by ring
  have hvertex : ∀ m : Fin 4, v m ∈ convexHull ℝ (Set.range v) := by
    intro m
    exact subset_convexHull ℝ (Set.range v) ⟨m, rfl⟩
  have hconv := convex_convexHull ℝ (Set.range v)
  have hleft := hconv (hvertex 0) (hvertex 3) (sub_nonneg.mpr hu1) hu0
    (by ring : 1-u+u = 1)
  have hright := hconv (hvertex 1) (hvertex 2) (sub_nonneg.mpr hu1) hu0
    (by ring : 1-u+u = 1)
  have hcomb := hconv hleft hright (sub_nonneg.mpr htheta1) htheta0
    (by ring : 1-theta+theta = 1)
  have hprod : theta*((1-u)*a+u*b)=X := by
    change (X/R)*R=X
    exact div_mul_cancel₀ X (ne_of_gt hRpos)
  have heq : (1-theta) • ((1-u) • v 0 + u • v 3) +
      theta • ((1-u) • v 1 + u • v 2) = z := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
      change (1-theta)*((1-u)*B+u*B) +
        theta*((1-u)*(B-n*a)+u*(B-n*b)) = z.re
      calc
        _ = B-n*(theta*((1-u)*a+u*b)) := by ring
        _ = B-n*X := by rw [hprod]
        _ = z.re := hzRe.symm
    · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
      change (1-theta)*((1-u)*tL+u*(tL+D)) +
        theta*((1-u)*tL+u*(tL+D)) = z.im
      calc
        _ = tL+u*D := by ring
        _ = z.im := by
          dsimp [u]
          field_simp [ne_of_gt hD]
          ring
  rw [heq] at hcomb
  exact hcomb

end ApollonianSuperharmonic

end
