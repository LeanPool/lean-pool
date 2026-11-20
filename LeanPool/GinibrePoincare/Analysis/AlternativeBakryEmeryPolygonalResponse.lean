/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryPolygonalResponse.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryCameronMartin
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryPolygonalNoise

/-! # Sharp response across finitely many polygonal control intervals
The actual controlled difference equation is integrated interval by interval;
no differentiability at the polygon's corners is required.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace GinibrePoincare
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

private def polygonResponseQ (κ ε t : ℝ) : ℝ :=
  bakryEmeryResponseCovariance κ t + ε * Real.exp (-2 * κ * t)

private theorem polygonResponseQ_pos {κ ε t : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (ht : 0 ≤ t) :
    0 < polygonResponseQ κ ε t := by
  have he : Real.exp (-2 * κ * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  exact add_pos_of_nonneg_of_pos
    (div_nonneg (sub_nonneg.mpr he) (by positivity)) (mul_pos hε (Real.exp_pos _))

private theorem polygonResponseQ_deriv (κ ε t : ℝ) (hκ : κ ≠ 0) :
    HasDerivAt (polygonResponseQ κ ε)
      (Real.exp (-2 * κ * t) - 2 * κ * ε * Real.exp (-2 * κ * t)) t := by
  have he := ((hasDerivAt_id t).const_mul (-2 * κ)).exp
  have hd := (((hasDerivAt_const t 1).sub he).div_const (2 * κ)).add (he.const_mul ε)
  convert hd using 1
  · funext s
    rfl
  · simp only [id_eq]
    field_simp
    ring

private theorem polygonResponseQ_ode (κ ε t : ℝ) (hκ : κ ≠ 0) :
    (Real.exp (-2 * κ * t) - 2 * κ * ε * Real.exp (-2 * κ * t)) +
      2 * κ * polygonResponseQ κ ε t = 1 := by
  unfold polygonResponseQ bakryEmeryResponseCovariance
  field_simp
  ring

omit [FiniteDimensional ℝ E] in
/-- Exact finite-grid response for the actual dissipative gradient state
comparison with constant controls `a j / sqrt(h)` on successive intervals.
The energy is exactly the Euclidean sum of squared increment coordinates. -/
theorem bakryEmeryLangevin_polygonal_response
    (W : E → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : Differentiable ℝ W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (m : ℕ) (h : ℝ) (hh : 0 < h) (a : ℕ → E) (X Y U : ℝ → E)
    (hU : ContinuousOn U (Icc 0 ((m : ℝ) * h))) (hU0 : U 0 = 0)
    (hXY : ∀ j < m, ∀ s ∈ Ioo ((j : ℝ) * h) ((j + 1 : ℕ) * h), X s - Y s = U s)
    (hEq : ∀ j < m, ∀ s ∈ Ioo ((j : ℝ) * h) ((j + 1 : ℕ) * h),
      HasDerivAt U (bakryEmeryLangevinDrift W (X s) -
        bakryEmeryLangevinDrift W (Y s) + (Real.sqrt h)⁻¹ • a j) s) :
    ‖U ((m : ℝ)*h)‖ ^ 2 ≤ bakryEmeryResponseCovariance κ ((m : ℝ)*h) *
      ∑ j ∈ Finset.range m, ‖a j‖ ^ 2 := by
  let A : ℕ → ℝ := fun k => ∑ j ∈ Finset.range k, ‖a j‖ ^ 2
  have hb (ε : ℝ) (hε : 0 < ε) :
      ‖U ((m : ℝ)*h)‖ ^ 2 ≤ polygonResponseQ κ ε ((m : ℝ)*h) * A m := by
    let q := polygonResponseQ κ ε
    let R : ℕ → ℝ := fun k => ‖U ((k : ℝ)*h)‖ ^ 2 / q ((k : ℝ)*h) - A k
    have hstep (j : ℕ) (hj : j < m) : R (j+1) ≤ R j := by
      let D : ℝ → ℝ := fun t => ‖U t‖ ^ 2 / q t -
        (A j + (t - (j : ℝ)*h) / h * ‖a j‖ ^ 2)
      have hs : Icc ((j : ℝ)*h) ((j+1 : ℕ)*h) ⊆ Icc 0 ((m : ℝ)*h) := by
        intro t ht
        constructor
        · exact (by positivity : 0 ≤ (j : ℝ)*h).trans ht.1
        · exact ht.2.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hh.le)
      have hqc : Continuous q := by unfold q polygonResponseQ bakryEmeryResponseCovariance; fun_prop
      have hdc : ContinuousOn D (Icc ((j : ℝ)*h) ((j+1 : ℕ)*h)) := by
        apply ((hU.mono hs).norm.pow 2 |>.div hqc.continuousOn
          (fun t ht => ne_of_gt (polygonResponseQ_pos hκ hε (hs ht).1))).sub
        fun_prop
      have hd (s : ℝ) (hs' : s ∈ Ioo ((j : ℝ)*h) ((j+1 : ℕ)*h)) :
          HasDerivAt D
            ((2 * inner ℝ (U s) (bakryEmeryLangevinDrift W (X s) -
              bakryEmeryLangevinDrift W (Y s) + (Real.sqrt h)⁻¹ • a j) * q s -
              ‖U s‖ ^ 2 * (Real.exp (-2 * κ * s) - 2 * κ * ε * Real.exp (-2 * κ * s))) /
              q s ^ 2 - ‖a j‖ ^ 2 / h) s := by
        have hbase := ((hEq j hj s hs').norm_sq).div (polygonResponseQ_deriv κ ε s hκ.ne')
          (ne_of_gt (polygonResponseQ_pos hκ hε ((by positivity : 0 ≤ (j : ℝ)*h).trans hs'.1.le)))
        have hjder := (hasDerivAt_const s (A j)).add
          ((((hasDerivAt_id s).sub_const ((j : ℝ)*h)).div_const h).mul_const (‖a j‖ ^ 2))
        convert hbase.sub hjder using 1
        · funext t
          rfl
        · dsimp only [q, id_eq]
          ring
      have hdn (s : ℝ) (hs' : s ∈ Ioo ((j : ℝ)*h) ((j+1 : ℕ)*h)) : deriv D s ≤ 0 := by
        rw [(hd s hs').deriv]
        have hq : 0 < q s := polygonResponseQ_pos hκ hε
          ((by positivity : 0 ≤ (j : ℝ)*h).trans hs'.1.le)
        let u := (Real.sqrt h)⁻¹ • a j
        have hdis := bakryEmeryLangevinDrift_dissipative W κ hc (X s) (Y s) (hW _) (hW _)
        rw [hXY j hj s hs'] at hdis
        have hyoung : 2 * q s * inner ℝ (U s) u ≤ ‖U s‖ ^ 2 + q s ^ 2 * ‖u‖ ^ 2 := by
          have hn := real_inner_self_nonneg (x := U s - q s • u)
          simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
            real_inner_self_eq_norm_sq, conj_trivial] at hn
          rw [real_inner_comm (U s) u] at hn
          nlinarith
        have hunorm : ‖u‖ ^ 2 = ‖a j‖ ^ 2 / h := by
          dsimp [u]
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hh)), mul_pow,
            inv_pow, Real.sq_sqrt hh.le]
          ring
        rw [hunorm] at hyoung
        have hode := polygonResponseQ_ode κ ε s hκ.ne'
        change (Real.exp (-2 * κ * s) - 2 * κ * ε * Real.exp (-2 * κ * s)) + 2 * κ * q s = 1 at hode
        rw [sub_nonpos, div_le_iff₀ (sq_pos_of_pos hq)]
        simp only [inner_add_right]
        nlinarith [mul_le_mul_of_nonneg_right hdis hq.le]
      have ha : AntitoneOn D (Icc ((j : ℝ)*h) ((j+1 : ℕ)*h)) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hdc
        · intro s hs'
          exact (hd s (by simpa only [interior_Icc] using
                            hs')).differentiableAt.differentiableWithinAt
        · intro s hs'
          exact hdn s (by simpa only [interior_Icc] using hs')
      have hle : (j : ℝ)*h ≤ (j+1 : ℕ)*h := by push_cast; nlinarith
      have hfinal := ha ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hle
      have hA : A (j+1) = A j + ‖a j‖ ^ 2 := Finset.sum_range_succ _ _
      simpa [D, R, hA, Nat.cast_add, Nat.cast_one, hh.ne', add_mul] using hfinal
    have hR : ∀ k ≤ m, R k ≤ 0 := by
      intro k hk
      induction k with
      | zero => simp [R, A, hU0]
      | succ k ih => exact (hstep k (by omega)).trans (ih (by omega))
    have hhR := hR m le_rfl
    have hratio : ‖U ((m : ℝ)*h)‖ ^ 2 / q ((m : ℝ)*h) ≤ A m := sub_nonpos.mp hhR
    exact (div_le_iff₀ (polygonResponseQ_pos hκ hε (by positivity))).mp hratio |>.trans_eq (mul_comm
        _ _)
  have ht : Tendsto (fun ε => polygonResponseQ κ ε ((m : ℝ)*h) * A m) (𝓝[>] 0)
      (𝓝 (bakryEmeryResponseCovariance κ ((m : ℝ)*h) * A m)) := by
    have hc' : Continuous (fun ε => polygonResponseQ κ ε ((m : ℝ)*h) * A m) := by
      unfold polygonResponseQ
      fun_prop
    simpa only [polygonResponseQ, zero_mul, add_zero] using
      (hc'.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht (by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hb ε hε)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Sharp Euclidean coordinate response for actual polygonally driven
Langevin corrections. The noise amplitude is explicit (`sqrt 2` for unit
diffusion); all control derivatives and their energy are proved internally. -/
theorem bakryEmeryLangevin_polygonal_noise_response
    (W : EuclideanSpace ℝ ι → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : Differentiable ℝ W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ / 2 * ‖x‖ ^ 2))
    (m : ℕ) (h : ℝ) (hh : 0 < h) (σ : ℝ)
    (x y : (Fin m × ι) → ℝ) (Y₀ Y₁ : ℝ → EuclideanSpace ℝ ι)
    (hY₀ : ContinuousOn Y₀ (Icc 0 ((m : ℝ) * h)))
    (hY₁ : ContinuousOn Y₁ (Icc 0 ((m : ℝ) * h))) (hinit : Y₁ 0 = Y₀ 0)
    (hEq₀ : ∀ s ∈ Ioo 0 ((m : ℝ) * h), HasDerivAt Y₀
      (bakryEmeryLangevinDrift W (Y₀ s + σ • bakryEmeryPolygonalNoise m h y s)) s)
    (hEq₁ : ∀ s ∈ Ioo 0 ((m : ℝ) * h), HasDerivAt Y₁
      (bakryEmeryLangevinDrift W (Y₁ s + σ • bakryEmeryPolygonalNoise m h x s)) s) :
    ‖(Y₁ ((m : ℝ)*h) + σ • bakryEmeryPolygonalNoise m h x ((m : ℝ)*h)) -
      (Y₀ ((m : ℝ)*h) + σ • bakryEmeryPolygonalNoise m h y ((m : ℝ)*h))‖ ^ 2 ≤
      (σ ^ 2 * bakryEmeryResponseCovariance κ ((m : ℝ)*h)) *
        ‖(WithLp.toLp 2 (x - y) : EuclideanSpace ℝ (Fin m × ι))‖ ^ 2 := by
  classical
  let X := fun s => Y₁ s + σ • bakryEmeryPolygonalNoise m h x s
  let Y := fun s => Y₀ s + σ • bakryEmeryPolygonalNoise m h y s
  let U := fun s => X s - Y s
  let a : ℕ → EuclideanSpace ℝ ι := fun j => if hj : j < m then
    σ • WithLp.toLp 2 (fun i => x (⟨j, hj⟩, i) - y (⟨j, hj⟩, i)) else 0
  have hU : ContinuousOn U (Icc 0 ((m : ℝ)*h)) :=
    (hY₁.add ((bakryEmeryPolygonalNoise_continuous m h x).const_smul σ).continuousOn).sub
      (hY₀.add ((bakryEmeryPolygonalNoise_continuous m h y).const_smul σ).continuousOn)
  have hU0 : U 0 = 0 := by
    dsimp [U, X, Y]
    rw [bakryEmeryPolygonalNoise_zero m h hh.le,
      bakryEmeryPolygonalNoise_zero m h hh.le, hinit]
    simp
  have hEq (j : ℕ) (hj : j < m) (s : ℝ)
      (hs : s ∈ Ioo ((j : ℝ)*h) ((j+1 : ℕ)*h)) :
      HasDerivAt U (bakryEmeryLangevinDrift W (X s) -
        bakryEmeryLangevinDrift W (Y s) + (Real.sqrt h)⁻¹ • a j) s := by
    have hs' : s ∈ Ioo 0 ((m : ℝ)*h) := ⟨
      (by positivity : 0 ≤ (j : ℝ)*h).trans_lt hs.1,
      hs.2.trans_le (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hh.le)⟩
    have hx := (bakryEmeryPolygonalNoise_hasDerivAt m h hh x ⟨j, hj⟩ s hs).const_smul σ
    have hy := (bakryEmeryPolygonalNoise_hasDerivAt m h hh y ⟨j, hj⟩ s hs).const_smul σ
    have hd := ((hEq₁ s hs').add hx).sub ((hEq₀ s hs').add hy)
    convert hd using 1
    dsimp only [X, Y, a]
    rw [dite_eq_left hj]
    have he : (Real.sqrt h)⁻¹ • (σ • WithLp.toLp 2
        (fun i => x (⟨j, hj⟩, i) - y (⟨j, hj⟩, i))) =
        σ • WithLp.toLp 2 (fun i => x (⟨j, hj⟩, i) / Real.sqrt h) -
        σ • WithLp.toLp 2 (fun i => y (⟨j, hj⟩, i) / Real.sqrt h) := by
      ext i
      simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      ring
    rw [he]
    abel
  have hb := bakryEmeryLangevin_polygonal_response W κ hκ hW hc m h hh a X Y U hU hU0
    (fun _ _ _ _ => rfl) hEq
  have henergy : (∑ j ∈ Finset.range m, ‖a j‖ ^ 2) =
      σ ^ 2 * ‖(WithLp.toLp 2 (x - y) : EuclideanSpace ℝ (Fin m × ι))‖ ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [a, dite_eq_left (Fin.isLt _), norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
    rw [Finset.mul_sum, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    rfl
  rw [henergy] at hb
  convert hb using 1
  ring

end
end GinibrePoincare
