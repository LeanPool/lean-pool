/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Analysis.BoxIntegral
public import LeanPool.ArnoldKAM.Arnold1963.Analysis.ContourShift
public import LeanPool.ArnoldKAM.Arnold1963.Basic.Functions

/-!
Coordinate induction extends the contour-shift identity to unit-cube integrals.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Complex
open scoped NNReal
namespace KamProject.Arnold1963

/-- A real coordinate vector shifted in the imaginary direction by another real vector. -/
def complexShift {n : ℕ} (y x : RealSpace n) : ComplexSpace n :=
  fun j => (x j : ℂ) + (y j : ℂ) * I

@[simp] theorem complexShift_zero {n : ℕ} (x : RealSpace n) :
    complexShift 0 x = complexify x := by ext j; simp [complexShift, complexify]

@[simp] theorem complexShift_cons {n : ℕ} (y : RealSpace (n + 1)) (x : ℝ)
    (t : RealSpace n) : complexShift y (Fin.cons x t) =
      Fin.cons ((x : ℂ) + y 0 * I) (complexShift (Fin.tail y) t) := by
  ext j
  exact Fin.cases rfl (fun _ => rfl) j

theorem complexShift_mem_strip {n : ℕ} {r : ℝ≥0} (y x : RealSpace n)
    (hy : ∀ j, |y j| ≤ r) : complexShift y x ∈ angleStrip n r := by
  apply (mem_angleStrip_iff _ _).mpr
  intro j
  simpa [complexShift] using hy j

theorem continuous_shift_slice {n : ℕ} {r : ℝ≥0} {f : ComplexSpace n → ℂ}
    (hf : ContinuousOn f (angleStrip n r)) (y : RealSpace n) (hy : ∀ j, |y j| ≤ r) :
    Continuous (fun x => f (complexShift y x)) :=
  hf.comp_continuous (by unfold complexShift; fun_prop)
    (fun x => complexShift_mem_strip y x hy)

private theorem analyticAt_cons_head {n : ℕ} (q : ComplexSpace n) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => (Fin.cons w q : ComplexSpace (n + 1))) z := by
  apply AnalyticAt.pi
  intro j
  exact Fin.cases analyticAt_id (fun _ => analyticAt_const) j

private theorem analyticAt_cons_tail {n : ℕ} (z : ℂ) (q : ComplexSpace n) :
    AnalyticAt ℂ (fun w : ComplexSpace n => (Fin.cons z w : ComplexSpace (n + 1))) q := by
  apply AnalyticAt.pi
  intro j
  refine Fin.cases analyticAt_const (fun i => ?_) j
  change AnalyticAt ℂ (fun x : ComplexSpace n => x i) q
  convert (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt q using 1
  rfl

private theorem cons_mem_strip {n : ℕ} {r : ℝ≥0} {z : ℂ} {q : ComplexSpace n}
    (hz : |z.im| ≤ r) (hq : q ∈ angleStrip n r) : Fin.cons z q ∈ angleStrip (n + 1) r := by
  apply (mem_angleStrip_iff _ _).mpr
  intro j
  exact Fin.cases hz (fun i => (mem_angleStrip_iff _ _).mp hq i) j

theorem integral_cons_horizontal_shift {n : ℕ} {r : ℝ≥0} {f : ComplexSpace (n + 1) → ℂ}
    (hf : AnalyticOnNhd ℂ f (angleStrip (n + 1) r))
    (hp : ∀ q ∈ angleStrip (n + 1) r, ∀ j,
      f (Function.update q j (q j + 1)) = f q)
    {q : ComplexSpace n} (hq : q ∈ angleStrip n r) {y : ℝ} (hy : |y| ≤ r) :
    (∫ x, f (Fin.cons ((x : ℂ) + y * I) q) ∂unitIntervalMeasure) =
      ∫ x, f (Fin.cons (x : ℂ) q) ∂unitIntervalMeasure := by
  have ht : ∀ t ∈ uIcc 0 y, |t| ≤ r := by
    intro t ht
    exact abs_le.mpr (uIcc_subset_Icc ⟨neg_nonpos.mpr r.coe_nonneg, r.coe_nonneg⟩
      (abs_le.mp hy) ht)
  have hd : DifferentiableOn ℂ (fun z => f (Fin.cons z q)) (uIcc 0 1 ×ℂ uIcc 0 y) := by
    intro z hz
    exact ((hf _ (cons_mem_strip (ht _ hz.2) hq)).comp
      (f := fun w : ℂ => (Fin.cons w q : ComplexSpace (n + 1)))
      (analyticAt_cons_head q z)).differentiableAt.differentiableWithinAt
  have hs := integral_horizontal_shift (fun z => f (Fin.cons z q)) 1 0 y hd (by
    intro t htt
    have hh := hp (Fin.cons ((t : ℂ) * I) q)
      (cons_mem_strip (by simpa using ht t htt) hq) 0
    have he : Function.update (Fin.cons ((t : ℂ) * I) q : ComplexSpace (n + 1)) 0
        ((t : ℂ) * I + 1) = Fin.cons (1 + (t : ℂ) * I) q := by
      ext j
      refine Fin.cases ?_ (fun i => ?_) j <;> simp [add_comm]
    simp only [Fin.cons_zero] at hh
    rw [he] at hh
    simpa only [ofReal_one] using hh)
  simp only [ofReal_zero, zero_mul, add_zero] at hs
  simpa only [integral_unitInterval_eq_interval] using hs.symm

theorem unitCubeIntegral_shift_eq {n : ℕ} {r : ℝ≥0} {f : ComplexSpace n → ℂ}
    (hf : AnalyticOnNhd ℂ f (angleStrip n r))
    (hp : ∀ q ∈ angleStrip n r, ∀ j, f (Function.update q j (q j + 1)) = f q)
    (y : RealSpace n) (hy : ∀ j, |y j| ≤ r) :
    unitCubeIntegral (fun x => f (complexShift y x)) =
      unitCubeIntegral (fun x => f (complexify x)) := by
  induction n with
  | zero =>
    apply unitCubeIntegral_congr
    intro x hx
    congr 1
    ext j
    exact Fin.elim0 j
  | succ n ih =>
    let y' : RealSpace (n + 1) := Fin.cons 0 (Fin.tail y)
    have hy' : ∀ j, |y' j| ≤ r := fun j =>
      Fin.cases (by simp [y']) (fun i => hy i.succ) j
    have hi (v : RealSpace (n + 1)) (hv : ∀ j, |v j| ≤ r) :
        Integrable (fun x => f (complexShift v x)) (unitCubeMeasure (n + 1)) :=
      integrable_unitCube (continuous_shift_slice hf.continuousOn v hv).continuousOn
    have hi0 : Integrable (fun x => f (complexify x)) (unitCubeMeasure (n + 1)) := by
      simpa using hi 0 (by intro j; simp)
    calc
      _ = ∫ t, (∫ x, f (Fin.cons ((x : ℂ) + y 0 * I)
          (complexShift (Fin.tail y) t)) ∂unitIntervalMeasure) ∂unitCubeMeasure n := by
        simpa only [complexShift_cons] using unitCubeIntegral_cons_symm (hi y hy)
      _ = ∫ t, (∫ x, f (Fin.cons (x : ℂ) (complexShift (Fin.tail y) t))
          ∂unitIntervalMeasure) ∂unitCubeMeasure n := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun t => integral_cons_horizontal_shift hf hp
          (complexShift_mem_strip _ _ (fun j => hy j.succ)) (hy 0)
      _ = unitCubeIntegral (fun x => f (complexShift y' x)) := by
        simpa [y'] using (unitCubeIntegral_cons_symm (hi y' hy')).symm
      _ = ∫ x, unitCubeIntegral (fun t => f (Fin.cons (x : ℂ)
          (complexShift (Fin.tail y) t))) ∂unitIntervalMeasure := by
        simpa [y'] using unitCubeIntegral_cons (hi y' hy')
      _ = ∫ x, unitCubeIntegral (fun t => f (Fin.cons (x : ℂ) (complexify t)))
          ∂unitIntervalMeasure := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro x
        apply ih (f := fun q => f (Fin.cons (x : ℂ) q))
        · intro q hq
          exact (hf _ (cons_mem_strip (by simp) hq)).comp
            (f := fun w => (Fin.cons (x : ℂ) w : ComplexSpace (n + 1)))
            (analyticAt_cons_tail _ q)
        · intro q hq j
          have hh := hp (Fin.cons (x : ℂ) q) (cons_mem_strip (by simp) hq) j.succ
          have he : Function.update (Fin.cons (x : ℂ) q : ComplexSpace (n + 1)) j.succ
              (q j + 1) =
                Fin.cons (x : ℂ) (Function.update q j (q j + 1)) := by
            ext i
            refine Fin.cases ?_ (fun k => ?_) i
            · rw [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero j))]
              rfl
            · simp [Function.update_apply]
          simp only [Fin.cons_succ] at hh
          rw [he] at hh
          exact hh
        · exact fun j => hy j.succ
      _ = _ := by
        have he (x : ℝ) (t : RealSpace n) :
            complexify (Fin.cons x t) = Fin.cons (x : ℂ) (complexify t) := by
          ext j
          exact Fin.cases rfl (fun _ => rfl) j
        simpa only [he] using (unitCubeIntegral_cons hi0).symm

end KamProject.Arnold1963
