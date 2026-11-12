/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3821T1LoopIndex
public import LeanPool.ApollonianSuperharmonic.P3821T1AngularIncrementLaws
public import Mathlib.Topology.Algebra.Order.Floor

-- [TABLET NODE: P3821T1LoopIndexLaws]

/-!
# P3821T1LoopIndexLaws

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace LoopIndexProof

private theorem integralIndex :
    (∀ (g : C((↑unitInterval : Type), ℂ)), ∀ (p : ℂ), (∀ (t : (↑unitInterval : Type)), (g :
        (↑unitInterval : Type) → ℂ) t ≠ p) → ∃ (theta : C((↑unitInterval : Type), ℝ)), (∀ (t :
            (↑unitInterval : Type)), Complex.exp ((↑((theta : (↑unitInterval : Type) → ℝ) t) : ℂ) *
        Complex.I) = ((g : (↑unitInterval : Type) → ℂ) t - p) / (↑‖(g : (↑unitInterval : Type) →
        ℂ) t - p‖ : ℂ)) ∧ (∀ (eta : C((↑unitInterval : Type), ℝ)), (∀ (t : (↑unitInterval :
        Type)), Complex.exp ((↑((eta : (↑unitInterval : Type) → ℝ) t) : ℂ) * Complex.I) = ((g :
        (↑unitInterval : Type) → ℂ) t - p) / (↑‖(g : (↑unitInterval : Type) → ℂ) t - p‖ : ℂ)) →
        (eta : (↑unitInterval : Type) → ℝ) ⟨(1 : ℝ), (by norm_num)⟩ -
        (eta : (↑unitInterval : Type) → ℝ) ⟨(0 : ℝ), (by norm_num)⟩ =
        P3821T1AngularIncrement g p) ∧ ((g : (↑unitInterval : Type) → ℂ) ⟨(0 : ℝ),
        (by norm_num)⟩ = (g : (↑unitInterval : Type) → ℂ) ⟨(1 : ℝ),
        (by norm_num)⟩ → ∃ (n : ℤ), P3821T1AngularIncrement g p = (2 :
        ℝ) * Real.pi * (↑n : ℝ))) → ((∀ (g : C(Circle, ℂ)), ∀ (p : ℂ), (∀ z, g z ≠ p) →
      ∃ n : ℤ, P3821T1LoopIndex g p = n)) := by
  classical
  intro hlift
  let q : C(unitInterval, Circle) :=
    ⟨fun t => Circle.exp (2 * Real.pi * (t : ℝ)), by fun_prop⟩
  intro g p hg
  let γ : C(unitInterval, ℂ) := g.comp q
  have havoid : ∀ t, γ t ≠ p := fun t => hg (q t)
  have hclose : γ 0 = γ 1 := by
    change g (q 0) = g (q 1)
    congr 1
    apply Circle.ext
    simp only [q, ContinuousMap.coe_mk, Circle.coe_exp]
    norm_num
  obtain ⟨_, _, _, hclosed⟩ := hlift γ p havoid
  obtain ⟨n, hn⟩ := hclosed hclose
  refine ⟨n, ?_⟩
  change P3821T1AngularIncrement γ p / (2 * Real.pi) = (n : ℝ)
  rw [hn]
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp

private theorem compositionIndex :
    (∀ (g : C((↑unitInterval : Type), ℂ)), ∀ (p : ℂ), (∀ (t : (↑unitInterval : Type)), (g :
        (↑unitInterval : Type) → ℂ) t ≠ p) → ∃ (theta : C((↑unitInterval : Type), ℝ)), (∀ (t :
            (↑unitInterval : Type)), Complex.exp ((↑((theta : (↑unitInterval : Type) → ℝ) t) : ℂ) *
        Complex.I) = ((g : (↑unitInterval : Type) → ℂ) t - p) / (↑‖(g : (↑unitInterval : Type) →
        ℂ) t - p‖ : ℂ)) ∧ (∀ (eta : C((↑unitInterval : Type), ℝ)), (∀ (t : (↑unitInterval :
        Type)), Complex.exp ((↑((eta : (↑unitInterval : Type) → ℝ) t) : ℂ) * Complex.I) = ((g :
        (↑unitInterval : Type) → ℂ) t - p) / (↑‖(g : (↑unitInterval : Type) → ℂ) t - p‖ : ℂ)) →
        (eta : (↑unitInterval : Type) → ℝ) ⟨(1 : ℝ), (by norm_num)⟩ -
        (eta : (↑unitInterval : Type) → ℝ) ⟨(0 : ℝ), (by norm_num)⟩ =
        P3821T1AngularIncrement g p) ∧ ((g : (↑unitInterval : Type) → ℂ) ⟨(0 : ℝ),
        (by norm_num)⟩ = (g : (↑unitInterval : Type) → ℂ) ⟨(1 : ℝ),
        (by norm_num)⟩ → ∃ (n : ℤ), P3821T1AngularIncrement g p = (2 :
        ℝ) * Real.pi * (↑n : ℝ))) → ((∀ (g : C(Circle, ℂ)), ∀ (alpha : C(Circle, Circle)), ∀ (p :
            ℂ), (∀ z, g z ≠ p) →
      P3821T1LoopIndex (g.comp alpha) p =
        P3821T1LoopIndex
          ((⟨fun z : Circle => (z : ℂ), continuous_subtype_val⟩ :
            C(Circle, ℂ)).comp alpha) 0 *
        P3821T1LoopIndex g p)) := by
  classical
  intro hlift
  let q : C(unitInterval, Circle) :=
    ⟨fun t => Circle.exp (2 * Real.pi * (t : ℝ)), by fun_prop⟩
  intro g alpha p hg
  let γ : C(unitInterval, ℂ) := g.comp q
  have havoid : ∀ t, γ t ≠ p := fun t => hg (q t)
  obtain ⟨theta, htheta, hthetaInd, hthetaClosed⟩ := hlift γ p havoid
  have hqclose : q 0 = q 1 := by
    apply Circle.ext
    simp only [q, ContinuousMap.coe_mk, Circle.coe_exp]
    norm_num
  have hclose : γ 0 = γ 1 := by
    change g (q 0) = g (q 1)
    exact congrArg g hqclose
  obtain ⟨m, hm⟩ := hthetaClosed hclose
  have hthetaDiff : theta 1 - theta 0 = 2 * Real.pi * (m : ℝ) := by
    calc
      theta 1 - theta 0 = P3821T1AngularIncrement γ p := by
        simpa using hthetaInd theta htheta
      _ = 2 * Real.pi * (m : ℝ) := hm
  let c : ℝ := 2 * Real.pi * (m : ℝ)
  let clamp01 : ℝ → ℝ := fun x => min 1 (max 0 x)
  have hmaxCont : Continuous (fun x : ℝ => max 0 x) :=
    continuous_max.comp (continuous_const.prodMk continuous_id)
  have hclampCont : Continuous clamp01 := by
    exact continuous_min.comp (continuous_const.prodMk hmaxCont)
  have hclampBounds (x : ℝ) : clamp01 x ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact le_min (by norm_num) (le_max_left _ _)
    · exact min_le_left _ _
  let f : ℝ → ℝ := fun x => theta ⟨clamp01 x, hclampBounds x⟩ - c * clamp01 x
  have hfCont : Continuous f := by
    apply Continuous.sub
    · exact theta.continuous.comp (Continuous.subtype_mk hclampCont hclampBounds)
    · exact continuous_const.mul hclampCont
  have hfEnds : f 0 = f 1 := by
    have h0 : clamp01 0 = 0 := by simp [clamp01]
    have h1 : clamp01 1 = 1 := by simp [clamp01]
    simp only [f, h0, h1]
    change theta ⟨0, by norm_num⟩ - c * 0 = theta ⟨1, by norm_num⟩ - c * 1
    dsimp [c]
    linarith [hthetaDiff]
  let Θ : C(ℝ, ℝ) :=
    ⟨fun x => f (Int.fract x) + c * x,
      (ContinuousOn.comp_fract'' hfCont.continuousOn hfEnds).add
        (continuous_const.mul continuous_id)⟩
  have hThetaShift (x : ℝ) (k : ℤ) :
      Θ (x + (k : ℝ)) = Θ x + c * (k : ℝ) := by
    simp only [Θ, ContinuousMap.coe_mk, Int.fract_add_intCast]
    ring
  have hThetaOn (x : unitInterval) : Θ (x : ℝ) = theta x := by
    by_cases hx : (x : ℝ) = 1
    · rw [show x = (1 : unitInterval) from Subtype.ext hx]
      have hfract1 : Int.fract (1 : ℝ) = 0 := by norm_num [Int.fract]
      change f (Int.fract (1 : ℝ)) + c * 1 = theta (1 : unitInterval)
      rw [hfract1]
      have hclamp0 : clamp01 0 = 0 := by simp [clamp01]
      simp only [f, hclamp0]
      simp only [mul_zero, sub_zero, mul_one]
      change theta ⟨0, by norm_num⟩ + c = theta ⟨1, by norm_num⟩
      dsimp [c]
      linarith [hthetaDiff]
    have hxlt : (x : ℝ) < 1 := lt_of_le_of_ne x.2.2 hx
    have hfract : Int.fract (x : ℝ) = (x : ℝ) :=
      Int.fract_eq_self.2 ⟨x.2.1, hxlt⟩
    have hclamp : clamp01 (x : ℝ) = (x : ℝ) := by
      simp [clamp01, x.2.1, le_of_lt hxlt]
    simp only [Θ, ContinuousMap.coe_mk, hfract, f, hclamp]
    ring
  let aLoop : C(unitInterval, ℂ) :=
    ⟨fun t => (alpha (q t) : ℂ), by fun_prop⟩
  have haAvoid : ∀ t, aLoop t ≠ 0 := by
    intro t hzero
    have := congrArg (fun z : ℂ => ‖z‖) hzero
    change ‖(alpha (q t) : ℂ)‖ = ‖(0 : ℂ)‖ at this
    rw [Circle.norm_coe, norm_zero] at this
    exact one_ne_zero this
  obtain ⟨a, ha, haInd, haClosed⟩ := hlift aLoop 0 haAvoid
  have haClose : aLoop 0 = aLoop 1 := by
    change (alpha (q 0) : ℂ) = (alpha (q 1) : ℂ)
    exact congrArg (fun z : Circle => (alpha z : ℂ)) hqclose
  obtain ⟨d, hd⟩ := haClosed haClose
  have haDiff : a 1 - a 0 = 2 * Real.pi * (d : ℝ) := by
    calc
      a 1 - a 0 = P3821T1AngularIncrement aLoop 0 := by
        simpa using haInd a ha
      _ = 2 * Real.pi * (d : ℝ) := hd
  have hidxG : P3821T1LoopIndex g p = (m : ℝ) := by
    change P3821T1AngularIncrement γ p / (2 * Real.pi) = (m : ℝ)
    rw [hm]
    field_simp
  let j : C(Circle, ℂ) := ⟨fun z => (z : ℂ), continuous_subtype_val⟩
  have hidxAlpha : P3821T1LoopIndex (j.comp alpha) 0 = (d : ℝ) := by
    change P3821T1AngularIncrement aLoop 0 / (2 * Real.pi) = (d : ℝ)
    rw [hd]
    field_simp
  let xMap : C(unitInterval, ℝ) :=
    ⟨fun t => a t / (2 * Real.pi), by fun_prop⟩
  let fracPoint (t : unitInterval) : unitInterval :=
    ⟨Int.fract (xMap t), Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hax (t : unitInterval) : a t = 2 * Real.pi * xMap t := by
    dsimp [xMap]
    field_simp
  have hfractFloor (t : unitInterval) :
      xMap t = Int.fract (xMap t) + (Int.floor (xMap t) : ℝ) :=
    (Int.fract_add_floor (xMap t)).symm
  have hqalpha (t : unitInterval) : q (fracPoint t) = alpha (q t) := by
    have haCircle : Circle.exp (a t) = alpha (q t) := by
      apply Circle.ext
      have ha' : Complex.exp ((a t : ℂ) * Complex.I) = (alpha (q t) : ℂ) := by
        simpa only [aLoop, ContinuousMap.coe_mk, sub_zero, Circle.norm_coe,
          Complex.ofReal_one, div_one] using ha t
      simpa only [Circle.coe_exp] using ha'
    calc
      q (fracPoint t) = Circle.exp (2 * Real.pi * Int.fract (xMap t)) := by
        rfl
      _ = Circle.exp (2 * Real.pi * Int.fract (xMap t) +
          2 * Real.pi * (Int.floor (xMap t) : ℝ)) := by
        calc
          _ = Circle.exp (2 * Real.pi * Int.fract (xMap t)) * 1 := by simp
          _ = Circle.exp (2 * Real.pi * Int.fract (xMap t)) *
              Circle.exp (2 * Real.pi * (Int.floor (xMap t) : ℝ)) := by
            rw [Circle.exp_two_pi_mul_int]
          _ = Circle.exp (2 * Real.pi * Int.fract (xMap t) +
              2 * Real.pi * (Int.floor (xMap t) : ℝ)) := by rw [Circle.exp_add]
      _ = Circle.exp (a t) := by
        congr 1
        calc
          2 * Real.pi * Int.fract (xMap t) + 2 * Real.pi * (Int.floor (xMap t) : ℝ) =
              2 * Real.pi * (Int.fract (xMap t) + (Int.floor (xMap t) : ℝ)) := by ring
          _ = 2 * Real.pi * xMap t := by rw [← hfractFloor t]
          _ = a t := (hax t).symm
      _ = alpha (q t) := haCircle
  let eta : C(unitInterval, ℝ) := Θ.comp xMap
  have heta (t : unitInterval) :
      Complex.exp ((eta t : ℂ) * Complex.I) =
        (g (alpha (q t)) - p) / (‖g (alpha (q t)) - p‖ : ℂ) := by
    let k := Int.floor (xMap t)
    have hThetaVal : Θ (xMap t) = theta (fracPoint t) + c * (k : ℝ) := by
      calc
        Θ (xMap t) = Θ (Int.fract (xMap t) + (k : ℝ)) := by
          exact congrArg Θ (hfractFloor t)
        _ = Θ (Int.fract (xMap t)) + c * (k : ℝ) := hThetaShift _ _
        _ = theta (fracPoint t) + c * (k : ℝ) := by
          change Θ (fracPoint t : ℝ) + c * (k : ℝ) = _
          rw [hThetaOn]
    have hc : c * (k : ℝ) = 2 * Real.pi * ((m * k : ℤ) : ℝ) := by
      dsimp [c]
      push_cast
      ring
    have hcircle : Circle.exp (Θ (xMap t)) = Circle.exp (theta (fracPoint t)) := by
      rw [hThetaVal, Circle.exp_add, hc, Circle.exp_two_pi_mul_int, mul_one]
    have hcomplex : Complex.exp ((Θ (xMap t) : ℂ) * Complex.I) =
        Complex.exp ((theta (fracPoint t) : ℂ) * Complex.I) := by
      have := congrArg (fun z : Circle => (z : ℂ)) hcircle
      simpa only [Circle.coe_exp] using this
    rw [show eta t = Θ (xMap t) from rfl, hcomplex, htheta (fracPoint t)]
    rw [show γ (fracPoint t) = g (alpha (q t)) by
      change g (q (fracPoint t)) = g (alpha (q t))
      rw [hqalpha t]]
  have hetaAll : ∀ t, Complex.exp ((eta t : ℂ) * Complex.I) =
      (((g.comp alpha).comp q t) - p) /
        (‖((g.comp alpha).comp q t) - p‖ : ℂ) := by
    intro t
    simpa only [ContinuousMap.comp_apply] using heta t
  have hcompAvoid : ∀ t, ((g.comp alpha).comp q) t ≠ p := by
    intro t
    exact hg (alpha (q t))
  obtain ⟨_, _, hcompInd, _⟩ := hlift ((g.comp alpha).comp q) p hcompAvoid
  have hEndShift : xMap 1 = xMap 0 + (d : ℝ) := by
    dsimp [xMap]
    field_simp
    nlinarith [haDiff]
  have hetaDiff : eta 1 - eta 0 = c * (d : ℝ) := by
    change Θ (xMap 1) - Θ (xMap 0) = _
    rw [hEndShift, hThetaShift]
    dsimp [c]
    ring
  have hcompInc :
      P3821T1AngularIncrement ((g.comp alpha).comp q) p = eta 1 - eta 0 := by
    exact (hcompInd eta hetaAll).symm
  have hidxComp : P3821T1LoopIndex (g.comp alpha) p = (m : ℝ) * (d : ℝ) := by
    change P3821T1AngularIncrement ((g.comp alpha).comp q) p /
        (2 * Real.pi) = (m : ℝ) * (d : ℝ)
    rw [hcompInc, hetaDiff]
    dsimp [c]
    field_simp
  change P3821T1LoopIndex (g.comp alpha) p =
    P3821T1LoopIndex (j.comp alpha) 0 * P3821T1LoopIndex g p
  rw [hidxComp, hidxAlpha, hidxG]
  ring

namespace HomotopyIndexProof

private theorem hlocal :
    (∀ (g : C((↑unitInterval : Type), ℂ)), ∀ (p : ℂ), (∀ (t : (↑unitInterval : Type)), (g :
        (↑unitInterval : Type) → ℂ) t ≠ p) → ∃ (theta : C((↑unitInterval : Type), ℝ)), (∀ (t :
        (↑unitInterval : Type)), Complex.exp ((↑((theta : (↑unitInterval : Type) → ℝ) t) : ℂ) *
        Complex.I) = ((g : (↑unitInterval : Type) → ℂ) t - p) / (↑‖(g : (↑unitInterval : Type) →
        ℂ) t - p‖ : ℂ)) ∧ (∀ (eta : C((↑unitInterval : Type), ℝ)), (∀ (t : (↑unitInterval :
        Type)), Complex.exp ((↑((eta : (↑unitInterval : Type) → ℝ) t) : ℂ) * Complex.I) = ((g :
        (↑unitInterval : Type) → ℂ) t - p) / (↑‖(g : (↑unitInterval : Type) → ℂ) t - p‖ : ℂ)) →
        (eta : (↑unitInterval : Type) → ℝ) ⟨(1 : ℝ), by norm_num⟩ - (eta : (↑unitInterval : Type)
            → ℝ) ⟨(0
        : ℝ), by norm_num⟩ = P3821T1AngularIncrement g p) ∧ ((g : (↑unitInterval : Type) → ℂ)
            ⟨(0 : ℝ),
        by norm_num⟩ = (g : (↑unitInterval : Type) → ℂ) ⟨(1 : ℝ), by norm_num⟩ → ∃ (n : ℤ),
            P3821T1AngularIncrement
        g p = (2 : ℝ) * Real.pi * (↑n : ℝ))) → (
    ∀ (H : C((↑unitInterval : Type) × Circle, ℂ)), ∀ (p : ℂ), (∀ (s : (↑unitInterval : Type)), ∀
        (z : Circle), (H : (↑unitInterval : Type) × Circle → ℂ) (s, z) ≠ p) → (∀ (avoid : ∀ (x :
        unitInterval × Circle), H x ≠ p),
    let normed : C(unitInterval × Circle, ℂ) :=
      ⟨fun x => (H x - p) / (‖H x - p‖ : ℂ), by
        apply Continuous.div
        · exact H.continuous.sub continuous_const
        · exact Complex.continuous_ofReal.comp (H.continuous.sub continuous_const).norm
        · intro x
          exact Complex.ofReal_ne_zero.mpr
            (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (avoid x)))⟩
    (∀ (x : unitInterval × Circle), ‖normed x‖ = 1) → ((UniformContinuous normed) → (
    let loopAt : unitInterval → C(Circle, ℂ) := fun s =>
      ⟨fun z => H (s, z), by fun_prop⟩
    let indexAt (s : unitInterval) : ℝ := P3821T1LoopIndex (loopAt s) p
    ∀ (s0 : unitInterval), ∃ δ > 0, ∀ s, dist s s0 < δ → indexAt s = indexAt s0)))) := by
  classical
  intro hlift H p hH avoid normed hnormed hUC loopAt indexAt s0
  let q : C(unitInterval, Circle) :=
    ⟨fun t => Circle.exp (2 * Real.pi * (t : ℝ)), by fun_prop⟩
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuous_iff.mp hUC) 1 zero_lt_one
  refine ⟨δ, hδ, ?_⟩
  intro s hs
  let ratio (z : Circle) : ℂ := normed (s, z) / normed (s0, z)
  have hclose (z : Circle) : dist (normed (s, z)) (normed (s0, z)) < 1 := by
    have hprod : dist (s, z) (s0, z) < δ := by simpa [Prod.dist_eq] using hs
    exact hmod hprod
  have hratioNorm (z : Circle) : ‖ratio z‖ = 1 := by
    simp [ratio, hnormed]
  have hratioNear (z : Circle) : ‖ratio z - 1‖ < 1 := by
    have hden : normed (s0, z) ≠ 0 := by
      intro hz
      have := congrArg (fun w : ℂ => ‖w‖) hz
      rw [hnormed] at this
      norm_num at this
    have heq : ratio z - 1 = (normed (s, z) - normed (s0, z)) / normed (s0, z) := by
      dsimp [ratio]
      field_simp
    rw [heq, norm_div, hnormed]
    simpa [dist_eq_norm] using hclose z
  have hratioRe (z : Circle) : 0 < (ratio z).re := by
    have hb := Complex.abs_re_le_norm (ratio z - 1)
    have hb' : |(ratio z).re - 1| < 1 := by
      have := lt_of_le_of_lt hb (hratioNear z)
      simpa using this
    rcases abs_lt.mp hb' with ⟨hlo, hhi⟩
    have hre : (ratio z).re - 1 > -1 := by linarith
    linarith
  have hratioCont : Continuous ratio := by
    apply Continuous.div
    · exact normed.continuous.comp (continuous_const.prodMk continuous_id)
    · exact normed.continuous.comp (continuous_const.prodMk continuous_id)
    · intro z hz
      have := congrArg (fun w : ℂ => ‖w‖) hz
      rw [hnormed] at this
      norm_num at this
  have hslit (z : Circle) : ratio z ∈ Complex.slitPlane := by
    exact Complex.mem_slitPlane_iff_not_le_zero.mpr
      (Complex.not_le_zero_iff.mpr (Or.inl (hratioRe z)))
  let argRatio : C(Circle, ℝ) :=
    ⟨fun z => Complex.arg (ratio z),
      continuousOn_univ.mp (Complex.continuousOn_arg.comp hratioCont.continuousOn
        (by intro z hz; exact hslit z))⟩
  have hargLift (z : Circle) :
      Complex.exp ((argRatio z : ℂ) * Complex.I) = ratio z := by
    have h := Complex.norm_mul_exp_arg_mul_I (ratio z)
    simpa [argRatio, hratioNorm z] using h
  let path0 : C(unitInterval, ℂ) := ⟨fun t => H (s0, q t), by fun_prop⟩
  let pathS : C(unitInterval, ℂ) := ⟨fun t => H (s, q t), by fun_prop⟩
  have hAvoid0 : ∀ t, path0 t ≠ p := fun t => hH s0 (q t)
  have hAvoidS : ∀ t, pathS t ≠ p := fun t => hH s (q t)
  obtain ⟨theta0, htheta0, hind0, _⟩ := hlift path0 p hAvoid0
  obtain ⟨_, _, hindS, _⟩ := hlift pathS p hAvoidS
  let argLoop : C(unitInterval, ℝ) := argRatio.comp q
  let eta : C(unitInterval, ℝ) :=
    ⟨fun t => theta0 t + argLoop t, theta0.continuous.add argLoop.continuous⟩
  have heta (t : unitInterval) :
      Complex.exp ((eta t : ℂ) * Complex.I) =
        (pathS t - p) / (‖pathS t - p‖ : ℂ) := by
    have hratio := hargLift (q t)
    have hbase := htheta0 t
    have hu0 : normed (s0, q t) =
        (path0 t - p) / (‖path0 t - p‖ : ℂ) := by rfl
    have hus : normed (s, q t) =
        (pathS t - p) / (‖pathS t - p‖ : ℂ) := by rfl
    have hmul : ratio (q t) * normed (s0, q t) = normed (s, q t) := by
      have hne : normed (s0, q t) ≠ 0 := by
        intro hz
        have := congrArg (fun w : ℂ => ‖w‖) hz
        rw [hnormed] at this
        norm_num at this
      change (normed (s, q t) / normed (s0, q t)) * normed (s0, q t) = _
      exact div_mul_cancel₀ _ hne
    have hmul' : normed (s0, q t) * ratio (q t) = normed (s, q t) := by
      rw [mul_comm, hmul]
    dsimp [eta, argLoop]
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, hratio, hbase]
    rw [← hu0, ← hus, hmul']
  have hqends : q 0 = q 1 := by
    apply Circle.ext
    simp only [q, ContinuousMap.coe_mk, Circle.coe_exp]
    norm_num
  have hargEnds : argLoop 0 = argLoop 1 := by
    change argRatio (q 0) = argRatio (q 1)
    rw [hqends]
  have hetaEnds : eta 1 - eta 0 = theta0 1 - theta0 0 := by
    dsimp [eta]
    rw [hargEnds]
    ring
  have hinc : P3821T1AngularIncrement pathS p =
      P3821T1AngularIncrement path0 p := by
    calc
      P3821T1AngularIncrement pathS p = eta 1 - eta 0 :=
        (hindS eta heta).symm
      _ = theta0 1 - theta0 0 := hetaEnds
      _ = P3821T1AngularIncrement path0 p := hind0 theta0 htheta0
  change P3821T1AngularIncrement ((loopAt s).comp q) p / (2 * Real.pi) =
    P3821T1AngularIncrement ((loopAt s0).comp q) p / (2 * Real.pi)
  rw [show (loopAt s).comp q = pathS by ext t; rfl,
    show (loopAt s0).comp q = path0 by ext t; rfl, hinc]

private theorem hnoLT :
    ∀ (H : C((↑unitInterval : Type) × Circle, ℂ)), ∀ (p : ℂ),
    let loopAt : unitInterval → C(Circle, ℂ) := fun s =>
      ⟨fun z => H (s, z), by fun_prop⟩
    let indexAt (s : unitInterval) : ℝ := P3821T1LoopIndex (loopAt s) p
    (∀ (s : unitInterval), ∃ n : ℤ, indexAt s = (n : ℝ)) → (
    let f : unitInterval → ℝ := indexAt
    (Continuous f) → ((∀ (n : ℤ), ∀ (s : unitInterval), f s ≠ (n : ℝ) + 1 / 2) → (
    let zero : unitInterval := ⟨0, by norm_num, by norm_num⟩
    let one : unitInterval := ⟨1, by norm_num, by norm_num⟩
    (IsPreconnected (Set.univ : Set unitInterval)) → (¬ f zero < f one)))) := by
  classical
  intro H p loopAt indexAt indexAt_int f hfCont hnotMid zero one hpc hlt
  obtain ⟨n0, hn0⟩ := indexAt_int zero
  obtain ⟨n1, hn1⟩ := indexAt_int one
  change f zero = (n0 : ℝ) at hn0
  change f one = (n1 : ℝ) at hn1
  rw [hn0, hn1] at hlt
  have hnlt : n0 < n1 := by
    exact_mod_cast hlt
  have hstep : n0 + 1 ≤ n1 := by omega
  have hstepR : (n0 : ℝ) + 1 ≤ (n1 : ℝ) := by exact_mod_cast hstep
  have hfx : (n0 : ℝ) + 1 / 2 < f one := by
    rw [hn1]
    linarith
  have hall := IsPreconnected.lt_of_ne (s := (Set.univ : Set unitInterval))
    (f := f) (b := (n0 : ℝ) + 1 / 2) hpc hfCont.continuousOn
    (fun s _ => hnotMid n0 s)
    (Exists.intro one (And.intro (Set.mem_univ one) hfx)) (Set.mem_univ zero)
  rw [hn0] at hall
  linarith

private theorem hnoGT :
    ∀ (H : C((↑unitInterval : Type) × Circle, ℂ)), ∀ (p : ℂ),
    let loopAt : unitInterval → C(Circle, ℂ) := fun s =>
      ⟨fun z => H (s, z), by fun_prop⟩
    let indexAt (s : unitInterval) : ℝ := P3821T1LoopIndex (loopAt s) p
    (∀ (s : unitInterval), ∃ n : ℤ, indexAt s = (n : ℝ)) → (
    let f : unitInterval → ℝ := indexAt
    (Continuous f) → ((∀ (n : ℤ), ∀ (s : unitInterval), f s ≠ (n : ℝ) + 1 / 2) → (
    let zero : unitInterval := ⟨0, by norm_num, by norm_num⟩
    let one : unitInterval := ⟨1, by norm_num, by norm_num⟩
    (IsPreconnected (Set.univ : Set unitInterval)) → (¬ f one < f zero)))) := by
  classical
  intro H p loopAt indexAt indexAt_int f hfCont hnotMid zero one hpc hgt
  obtain ⟨n0, hn0⟩ := indexAt_int zero
  obtain ⟨n1, hn1⟩ := indexAt_int one
  change f zero = (n0 : ℝ) at hn0
  change f one = (n1 : ℝ) at hn1
  rw [hn0, hn1] at hgt
  have hnlt : n1 < n0 := by
    exact_mod_cast hgt
  have hstep : n1 + 1 ≤ n0 := by omega
  have hstepR : (n1 : ℝ) + 1 ≤ (n0 : ℝ) := by exact_mod_cast hstep
  have hfx : (n1 : ℝ) + 1 / 2 < f zero := by
    rw [hn0]
    linarith
  have hall := IsPreconnected.lt_of_ne (s := (Set.univ : Set unitInterval))
    (f := f) (b := (n1 : ℝ) + 1 / 2) hpc hfCont.continuousOn
    (fun s _ => hnotMid n1 s)
    (Exists.intro zero (And.intro (Set.mem_univ zero) hfx)) (Set.mem_univ one)
  rw [hn1] at hall
  linarith

end HomotopyIndexProof

private theorem homotopyIndex :
    (∀ (g : C((↑unitInterval : Type), ℂ)), ∀ (p : ℂ), (∀ (t : (↑unitInterval : Type)), (g :
        (↑unitInterval : Type) → ℂ) t ≠ p) → ∃ (theta : C((↑unitInterval : Type), ℝ)), (∀ (t :
            (↑unitInterval : Type)), Complex.exp ((↑((theta : (↑unitInterval : Type) → ℝ) t) : ℂ) *
        Complex.I) = ((g : (↑unitInterval : Type) → ℂ) t - p) / (↑‖(g : (↑unitInterval : Type) →
        ℂ) t - p‖ : ℂ)) ∧ (∀ (eta : C((↑unitInterval : Type), ℝ)), (∀ (t : (↑unitInterval :
        Type)), Complex.exp ((↑((eta : (↑unitInterval : Type) → ℝ) t) : ℂ) * Complex.I) = ((g :
        (↑unitInterval : Type) → ℂ) t - p) / (↑‖(g : (↑unitInterval : Type) → ℂ) t - p‖ : ℂ)) →
        (eta : (↑unitInterval : Type) → ℝ) ⟨(1 : ℝ), (by norm_num)⟩ -
        (eta : (↑unitInterval : Type) → ℝ) ⟨(0 : ℝ), (by norm_num)⟩ =
        P3821T1AngularIncrement g p) ∧ ((g : (↑unitInterval : Type) → ℂ) ⟨(0 : ℝ),
        (by norm_num)⟩ = (g : (↑unitInterval : Type) → ℂ) ⟨(1 : ℝ),
        (by norm_num)⟩ → ∃ (n : ℤ), P3821T1AngularIncrement g p = (2 :
        ℝ) * Real.pi * (↑n : ℝ))) → ((∀ (H : C(unitInterval × Circle, ℂ)), ∀ (p : ℂ), (∀ s z, H
        (s, z) ≠ p) →
      P3821T1LoopIndex
        ⟨fun z => H (⟨0, by norm_num⟩, z), by fun_prop⟩ p =
      P3821T1LoopIndex
        ⟨fun z => H (⟨1, by norm_num⟩, z), by fun_prop⟩ p)) := by
  classical
  intro hlift
  let q : C(unitInterval, Circle) :=
    ⟨fun t => Circle.exp (2 * Real.pi * (t : ℝ)), by fun_prop⟩
  intro H p hH
  let avoid (x : unitInterval × Circle) : H x ≠ p := hH x.1 x.2
  let normed : C(unitInterval × Circle, ℂ) :=
    ⟨fun x => (H x - p) / (‖H x - p‖ : ℂ), by
      apply Continuous.div
      · exact H.continuous.sub continuous_const
      · exact Complex.continuous_ofReal.comp (H.continuous.sub continuous_const).norm
      · intro x
        exact Complex.ofReal_ne_zero.mpr
          (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (avoid x)))⟩
  have hnormed (x : unitInterval × Circle) : ‖normed x‖ = 1 := by
    change ‖(H x - p) / (‖H x - p‖ : ℂ)‖ = 1
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    exact div_self (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (avoid x)))
  have hUC : UniformContinuous normed :=
    CompactSpace.uniformContinuous_of_continuous normed.continuous
  let loopAt : unitInterval → C(Circle, ℂ) := fun s =>
    ⟨fun z => H (s, z), by fun_prop⟩
  let indexAt (s : unitInterval) : ℝ := P3821T1LoopIndex (loopAt s) p
  have indexAt_int (s : unitInterval) : ∃ n : ℤ, indexAt s = (n : ℝ) := by
    let pathS : C(unitInterval, ℂ) := ⟨fun t => H (s, q t), by fun_prop⟩
    obtain ⟨thetaS, _, _, hclosedS⟩ := hlift
      pathS p (fun t => hH s (q t))
    have hqcloseS : q 0 = q 1 := by
      apply Circle.ext
      simp only [q, ContinuousMap.coe_mk, Circle.coe_exp]
      norm_num
    have hcloseS : pathS 0 = pathS 1 :=
      congrArg (fun z : Circle => H (s, z)) hqcloseS
    obtain ⟨n, hn⟩ := hclosedS hcloseS
    refine ⟨n, ?_⟩
    change P3821T1AngularIncrement ((loopAt s).comp q) p /
      (2 * Real.pi) = (n : ℝ)
    rw [show (loopAt s).comp q = pathS by ext t; rfl]
    rw [hn]
    field_simp
  have hlocal (s0 : unitInterval) :
      ∃ δ > 0, ∀ s, dist s s0 < δ → indexAt s = indexAt s0 := HomotopyIndexProof.hlocal hlift H p
          hH avoid hnormed hUC s0
  let f : unitInterval → ℝ := indexAt
  have hfCont : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro s0
    obtain ⟨δ, hδ, hl⟩ := hlocal s0
    change Filter.Tendsto f (nhds s0) (nhds (f s0))
    have hc : Filter.Tendsto (fun _ : unitInterval => f s0)
        (nhds s0) (nhds (f s0)) := tendsto_const_nhds
    have heq : (fun _ : unitInterval => f s0) =ᶠ[nhds s0] f := by
      filter_upwards [Metric.ball_mem_nhds s0 hδ] with s hs
      exact (hl s hs).symm
    exact (Filter.tendsto_congr' heq).mp hc
  have hfractIndex (s : unitInterval) : Int.fract (f s) = 0 := by
    obtain ⟨n, hn⟩ := indexAt_int s
    change f s = (n : ℝ) at hn
    rw [hn]
    simp
  have hfractHalf (n : ℤ) : Int.fract ((n : ℝ) + 1 / 2) = 1 / 2 := by
    rw [Int.fract_intCast_add]
    norm_num [Int.fract]
  have hnotMid (n : ℤ) (s : unitInterval) : f s ≠ (n : ℝ) + 1 / 2 := by
    intro heq
    have hzero := hfractIndex s
    have hfrac := congrArg Int.fract heq
    rw [hzero, hfractHalf] at hfrac
    norm_num at hfrac
  let zero : unitInterval := ⟨0, by norm_num, by norm_num⟩
  let one : unitInterval := ⟨1, by norm_num, by norm_num⟩
  have hpc : IsPreconnected (Set.univ : Set unitInterval) :=
    PreconnectedSpace.isPreconnected_univ
  have hnoLT : ¬ f zero < f one := HomotopyIndexProof.hnoLT H p indexAt_int hfCont hnotMid hpc
  have hnoGT : ¬ f one < f zero := HomotopyIndexProof.hnoGT H p indexAt_int hfCont hnotMid hpc
  have hends : f zero = f one := by
    rcases lt_trichotomy (f zero) (f one) with hlt | heq | hgt
    · exact (hnoLT hlt).elim
    · exact heq
    · exact (hnoGT hgt).elim
  change P3821T1LoopIndex (loopAt zero) p =
    P3821T1LoopIndex (loopAt one) p
  exact hends

end LoopIndexProof

theorem P3821T1LoopIndexLaws :
    (∀ (g : C(Circle, ℂ)) (p : ℂ), (∀ z, g z ≠ p) →
      ∃ n : ℤ, P3821T1LoopIndex g p = n) ∧
    (∀ (g : C(Circle, ℂ)) (alpha : C(Circle, Circle)) (p : ℂ),
      (∀ z, g z ≠ p) →
      P3821T1LoopIndex (g.comp alpha) p =
        P3821T1LoopIndex
          ((⟨fun z : Circle => (z : ℂ), continuous_subtype_val⟩ :
            C(Circle, ℂ)).comp alpha) 0 *
        P3821T1LoopIndex g p) ∧
    (∀ (H : C(unitInterval × Circle, ℂ)) (p : ℂ),
      (∀ s z, H (s, z) ≠ p) →
      P3821T1LoopIndex
        ⟨fun z => H (⟨0, by norm_num⟩, z), by fun_prop⟩ p =
      P3821T1LoopIndex
        ⟨fun z => H (⟨1, by norm_num⟩, z), by fun_prop⟩ p) := by
-- BODY
  classical
  let q : C(unitInterval, Circle) :=
    ⟨fun t => Circle.exp (2 * Real.pi * (t : ℝ)), by fun_prop⟩
  rcases P3821T1AngularIncrementLaws with ⟨hlift, _, _⟩
  have integralIndex :
      (∀ (g : C(Circle, ℂ)) (p : ℂ), (∀ z, g z ≠ p) →
      ∃ n : ℤ, P3821T1LoopIndex g p = n) := LoopIndexProof.integralIndex hlift
  have compositionIndex :
      (∀ (g : C(Circle, ℂ)) (alpha : C(Circle, Circle)) (p : ℂ),
      (∀ z, g z ≠ p) →
      P3821T1LoopIndex (g.comp alpha) p =
        P3821T1LoopIndex
          ((⟨fun z : Circle => (z : ℂ), continuous_subtype_val⟩ :
            C(Circle, ℂ)).comp alpha) 0 *
        P3821T1LoopIndex g p) := LoopIndexProof.compositionIndex hlift
  have homotopyIndex :
      (∀ (H : C(unitInterval × Circle, ℂ)) (p : ℂ),
      (∀ s z, H (s, z) ≠ p) →
      P3821T1LoopIndex
        ⟨fun z => H (⟨0, by norm_num⟩, z), by fun_prop⟩ p =
      P3821T1LoopIndex
        ⟨fun z => H (⟨1, by norm_num⟩, z), by fun_prop⟩ p) := LoopIndexProof.homotopyIndex hlift
  exact ⟨integralIndex, compositionIndex, homotopyIndex⟩

end ApollonianSuperharmonic

end
