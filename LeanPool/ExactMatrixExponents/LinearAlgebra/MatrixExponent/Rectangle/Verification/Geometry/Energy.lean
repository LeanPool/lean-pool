/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Profile.Root
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Multi.Radial

/-! # Variational bounds for the tripod -/

@[expose] public section

section
/- # The variational energy near an axis -/

namespace MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Energy
open Minimum Profile

variable {D : Vec → ℝ} {P : PairPrices} {v : Vec} {R : Vec → ℝ} {i j k : Fin 3}

private theorem Root.upper (h : Root D v R P) (hv : Positive v) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (x : Vec) (hx : Positive x) :
    R x ≤ intercept P (opposite v) (criticalWidth v) i +
      Profile.residual D v i * Real.log (x i / criticalWidth v i) +
      (v j)⁻¹ * Real.log (x j + x i) + (v k)⁻¹ * Real.log (x k + x i) := by
  have hu := critical_pos hv
  have hd := opposite_pos hv
  have h₁ := (h.family.envelope hu hd hij (hx i) (hx j)).2
  have h₂ := (h.family.envelope hu hd hik (hx i) (hx k)).2
  apply le_of_mul_le_mul_left _ (hd i)
  refine (h.chord _ _ _ hij hik hjk x hx).trans ?_
  refine (add_le_add (mul_le_mul_of_nonneg_left h₁ (inv_pos.mpr (hv j)).le)
    (mul_le_mul_of_nonneg_left h₂ (inv_pos.mpr (hv k)).le)).trans_eq ?_
  unfold model Profile.residual
  rw [opposite_eq v hij hik hjk]
  ring

private theorem near_cost (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (r : ℝ) (x : Vec) :
    cost (near i r / v) x = (v i)⁻¹ * x i + r * (v j)⁻¹ * x j + r * (v k)⁻¹ * x k := by
  change mass _ = _
  rw [mass_eq _ hij hik hjk]
  simp only [Pi.div_apply, near, ite_true, ite_eq_right hij.symm, ite_eq_right hik.symm,
    div_eq_mul_inv, one_mul]

private theorem scaled_max {u a b x : ℝ} (hu : 0 < u) (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    b * Real.log (x / u) - a * x ≤ b * Real.log (b / (a * u)) - b := by
  rw [Real.log_div hx.ne' hu.ne', ← div_div, Real.log_div (div_pos hb ha).ne' hu.ne']
  linarith only [log_max hb ha hx]

private theorem unit_max {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    Real.log x - r * x ≤ -Real.log r - 1 := by
  simpa only [one_mul, one_div, Real.log_inv] using log_max zero_lt_one hr hx

theorem Root.axis_upper (h : Root D v R P) (hv : Positive v) (i : Fin 3)
    (hb : 0 < Profile.residual D v i) {r : ℝ} (hr : 0 < r) (ha : 0 < (v i)⁻¹ - r * opposite v i) :
    variational R (D v⁻¹) (near i r / v) + opposite v i * Real.log r ≤
      intercept P (opposite v) (criticalWidth v) i + Profile.residual D v i *
        Real.log (Profile.residual D v i / (((v i)⁻¹ - r * opposite v i) * criticalWidth v i)) := by
  let j := i + 1
  let k := i + 2
  have hij : i ≠ j := by unfold j; omega
  have hik : i ≠ k := by unfold k; omega
  have hjk : j ≠ k := by unfold j k; omega
  apply le_sub_iff_add_le.mp
  apply variational_le
  intro x hx
  have h₁ := scaled_max (critical_pos hv i) ha hb (hx i)
  have h₂ := mul_le_mul_of_nonneg_left (unit_max hr (add_pos (hx j) (hx i))) (inv_pos.mpr (hv j)).le
  have h₃ := mul_le_mul_of_nonneg_left (unit_max hr (add_pos (hx k) (hx i))) (inv_pos.mpr (hv k)).le
  have hu := h.upper hv hij hik hjk x hx
  rw [near_cost hij hik hjk]
  simp only [Profile.residual, opposite_eq v hij hik hjk] at hu h₁ ⊢
  linarith only [hu, h₁, h₂, h₃]

theorem Root.axis_lower (h : Root D v R P) (hv : Positive v) (i : Fin 3)
    (hb : 0 < Profile.residual D v i) {r : ℝ} (hr : 0 < r) :
    axisValue D v P i - r * (v (i + 2))⁻¹ * (Profile.residual D v i * v i) ≤
      variational R (D v⁻¹) (near i r / v) + opposite v i * Real.log r := by
  let j := i + 1
  let k := i + 2
  have hij : i ≠ j := by unfold j; omega
  have hik : i ≠ k := by unfold k; omega
  have hjk : j ≠ k := by unfold j k; omega
  let X := Profile.residual D v i * v i
  have hX : 0 < X := mul_pos hb (hv i)
  let x : Vec := fun l => if l = i then X else if l = j then r⁻¹ else X + r⁻¹
  have hx : Positive x := by intro l; unfold x; split_ifs <;> positivity
  have hxi : x i = X := by simp [x]
  have hxj : x j = r⁻¹ := by simp [x, hij.symm]
  have hxk : x k = X + r⁻¹ := by simp [x, hik.symm, hjk.symm]
  have hu := (h.family.envelope (critical_pos hv) (opposite_pos hv) hij (hx i) (hx j)).1
  have hp := h.pairing _ _ _ hij hik hjk x hx (by rw [hxi, hxj, hxk])
  have hs : Positive (near i r / v) := by
    intro l
    apply div_pos _ (hv l)
    unfold near
    split <;> positivity
  have he := h.growth.lower hs hx
  have hcost : cost (near i r / v) x = D v⁻¹ + r * (v k)⁻¹ * X := by
    rw [near_cost hij hik hjk, hxi, hxj, hxk]
    have hi : (v i)⁻¹ * X = Profile.residual D v i := by
      unfold X; rw [mul_left_comm, inv_mul_cancel₀ (hv i).ne', mul_one]
    have ht (a : ℝ) : r * a * r⁻¹ = a := by rw [mul_right_comm, mul_inv_cancel₀ hr.ne', one_mul]
    rw [hi, mul_add, ht, ht, Profile.residual, opposite_eq v hij hik hjk]
    ring
  rw [hcost] at he
  have hlo := hu.trans hp
  rw [model, hxi, hxj, Real.log_inv] at hlo
  have heq : X / criticalWidth v i = Profile.residual D v i / ((v i)⁻¹ * criticalWidth v i) := by
    simp [X, div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
  rw [heq] at hlo
  change axisValue D v P i - r * (v k)⁻¹ * X ≤ _
  unfold axisValue Profile.residual at *
  linarith only [hlo, he]

end MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Energy
end

section
/-
# From radial energy contraction to spectral propagation

The test widths and the chord estimate give matching one-sided
limits at each axis. The intercept comparison controls their
differences uniformly up to a reciprocal face.
-/

namespace MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Energy
open Profile Minimum Set Filter
open scoped Topology

variable {F : Type} [Field F] {D : Vec → ℝ} {R : Vec → Vec → ℝ}
  {P : PairPrices} {v : Vec}

private theorem near_potential (i : Fin 3) (r : ℝ) :
    potential (adjusted D R) v (near i r) =
      variational (R v⁻¹) (D v⁻¹) (near i r / v) + opposite v i * Real.log r -
        (mass v)⁻¹ * Real.log (1 + 2 * r) := by
  unfold potential adjusted opposite mass
  fin_cases i <;> simp [near, Fin.sum_univ_three] <;> ring_nf

theorem Root.axis_limit (h : Root D v (R v⁻¹) P) (hd : StarTripod F D)
    (hv : Positive v) (i : Fin 3) :
    Tendsto (fun r => potential (adjusted D R) v (near i r)) (𝓝[>] 0)
      (𝓝 (axisValue D v P i)) := by
  let a := (v i)⁻¹
  let d := opposite v i
  let B := Profile.residual D v i
  let u := criticalWidth v i
  let C := intercept P (opposite v) (criticalWidth v) i
  have ha : 0 < a := inv_pos.mpr (hv i)
  have hB : 0 < B := (residual_bounds hd hv i).1
  have hu : 0 < u := critical_pos hv i
  let lo (r : ℝ) := axisValue D v P i - r * (v (i + 2))⁻¹ * (B * v i)
  let hi (r : ℝ) := C + B * Real.log (B / ((a - r * d) * u))
  let g (r : ℝ) := variational (R v⁻¹) (D v⁻¹) (near i r / v) + d * Real.log r
  have hlo : ContinuousAt lo 0 := by unfold lo; fun_prop
  have hhi : ContinuousAt hi 0 := by
    unfold hi
    fun_prop (disch := simp [ha.ne', hu.ne', hB.ne'])
  have hl₀ : lo 0 = axisValue D v P i := by simp [lo]
  have hh₀ : hi 0 = axisValue D v P i := by simp [hi, axisValue, C, B, a, u]
  have hn : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < a - r * d := by
    have he : ContinuousAt (fun r : ℝ => a - r * d) 0 := by fun_prop
    exact he.continuousWithinAt.eventually_const_lt (by simpa using ha)
  have hg : Tendsto g (𝓝[>] 0) (𝓝 (axisValue D v P i)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (hl₀ ▸ hlo.continuousWithinAt.tendsto) (hh₀ ▸ hhi.continuousWithinAt.tendsto) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact h.axis_lower hv i hB hr
    · filter_upwards [self_mem_nhdsWithin, hn] with r hr ha'
      exact h.axis_upper hv i hB hr ha'
  have hx : ContinuousAt (fun r : ℝ => (mass v)⁻¹ * Real.log (1 + 2 * r)) 0 := by
    fun_prop (disch := norm_num)
  simp_rw [near_potential]
  simpa only [mul_zero, add_zero, Real.log_one, sub_zero, g] using hg.sub hx.continuousWithinAt

/-- All costs increase by the same amount. Initial costs are
proportional to the arm lengths when the terminals move. -/
def Contracts (D : Vec → ℝ) (R : Vec → Vec → ℝ) : Prop :=
  ∀ v w s, Positive v → Positive w → Positive s → v ≤ w → ∀ t : ℝ, 0 < t →
    adjusted D R w s - adjusted D R w (s + t • w) ≤
      adjusted D R v s - adjusted D R v (s + t • v)

theorem uniform_of_contraction (hd : StarTripod F D)
    (h : ∀ v, Positive v → ∃ P, Root D v (R v⁻¹) P) (hc : Contracts D R) :
    Face.Uniform (defect D) := by
  have hp {v s : Vec} (hv : Positive v) (hs : Positive s) : Positive (s / v) :=
    fun i => div_pos (hs i) (hv i)
  have hr : Radial D (adjusted D R) := by
    refine ⟨?_, ?_, hc⟩
    · intro v hv
      obtain ⟨P, hP⟩ := h v hv
      exact hP.growth.continuous.comp (by fun_prop (disch := exact (hv _).ne'))
        (fun _ hs => hp hv hs)
    · intro v s hv hs t ht
      obtain ⟨P, hP⟩ := h v hv
      unfold adjusted
      rw [show (t • s) / v = t • (s / v) by ext i; simp [mul_div_assoc]]
      exact hP.growth.log_scale (hp hv hs) ht
  apply hr.uniform hd
  apply axisLimits hd
  intro v hv
  obtain ⟨P, hP⟩ := h v hv
  exact ⟨P, hP.family, hP.axis_limit hd hv⟩

end MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Energy
end

section
/- Radial contraction on the three rays controls the tripod defect uniformly. -/

namespace MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Twig
open Energy Minimum Profile

variable {K : Type} [Field K] {A : MatrixExponent.Prices.Atlas K Twig}

private theorem adjusted_eq {v : Vec} (hv : Positive v) (s : Vec) :
    adjusted (label A) (rootPrices A) v s = Multi.Q A origin (mark v⁻¹) (s / v) := by
  unfold Multi.Q
  rw [← rootPlacement,
    root_label A (a := v⁻¹) (fun i => inv_pos.mpr (hv i))]
  rfl

variable [Infinite K]

private theorem Homogeneous.contracts (hA : Homogeneous A) : Contracts (label A) (rootPrices A)
    := by
  intro v w s hv hw hs hvw t ht
  have hp (z : Vec) (hz : Positive z) : Positive z⁻¹ := fun i => inv_pos.mpr (hz i)
  have hl (z : Vec) (hz : Positive z) : 0 < A.price (Multi.sites origin (mark z⁻¹)) 2 := by
    rw [← rootPlacement, root_label A (hp z hz)]
    exact hA.star.pos _ (hp z hz)
  have hm (z : Vec) (hz : Positive z) (i) : Dist.dist origin (mark z⁻¹ i) = (z i)⁻¹ := by
    simp [mark, radius, (hz i).le]
  have hd (z : Vec) (hz : Positive z) :
      (s + t • z) / z = (fun i => (s / z) i + t) := by
    funext i
    simp [add_div, (hz i).ne']
  rw [adjusted_eq hw, adjusted_eq hw, adjusted_eq hv, adjusted_eq hv, hd w hw, hd v hv]
  refine Multi.Q_contract A origin (mark v⁻¹) (mark w⁻¹) (s / v) (s / w) (v / w)
    (fun i => (div_pos (hv i) (hw i)).le) (fun i => (div_le_one (hw i)).mpr (hvw i))
    ?_ ?_ ?_ (fun i => div_pos (hs i) (hv i)) (fun i => div_pos (hs i) (hw i))
    (hl v hv) (hl w hw) ht.le
  · intro i
    rw [hm v hv, hm w hw, Pi.div_apply]
    field_simp [(hv i).ne', (hw i).ne']
  · intro i
    rw [hm v hv, mark_dist (hp w hw) (hp v hv), ite_eq_left rfl]
    simp only [Pi.inv_apply, Pi.div_apply]
    rw [abs_of_nonpos (sub_nonpos.mpr (inv_anti₀ (hv i) (hvw i)))]
    field_simp [(hv i).ne', (hw i).ne']; ring
  · intro i
    apply le_of_eq
    simp only [Pi.div_apply]
    field_simp [(hv i).ne', (hw i).ne']

theorem Homogeneous.uniform (hA : Homogeneous A) : Face.Uniform (defect (label A)) := by
  apply uniform_of_contraction hA.star _ hA.contracts
  intro v hv
  refine ⟨_, root A hA hv ?_⟩
  apply family A (mark v⁻¹) _ _ (critical_pos hv) (opposite_pos hv)
  intro i j k hij hik hjk
  have ha : Positive v⁻¹ := fun l => inv_pos.mpr (hv l)
  rw [mark_dist ha ha, ite_eq_right hjk, opposite_eq v hij hik hjk]
  rfl

end MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Twig
end
