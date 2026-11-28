/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Cube.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Finite-rank kernel operators and their action on slices

A **finite-rank kernel operator** on functions on `[0, 1]` is `T g = ∑_j (∫_0^1 g κ_j) φ_j`,
with finitely many bounded measurable kernels `κ_j` and functions `φ_j` (`Cube.KernelOp`). The
local projections onto piecewise polynomials and the spline quasi-interpolants are of this form.

On the cube `T` acts on the slices in a coordinate `i`: `T^{(i)} g(x) = T(slice g x i)(x_i)`
(`Cube.KernelOp.slicewise`). The result has the **form of `T` in coordinate `i`**,
`g(x) = ∑_j c_j(x) φ_j(x_i)` with bounded measurable coefficients `c_j` that do not depend on
`x_i` (`Cube.KernelOp.IsForm`, `Cube.KernelOp.isForm_slicewise`), and the action of a kernel
operator in another coordinate keeps this form (`Cube.KernelOp.IsForm.slicewise`): it only
integrates the coefficients, by linearity of the integral over finite sums. Applying `T` in all
coordinates one after another (`Cube.KernelOp.foldSlicewise`) therefore gives a function with the
form of `T` in every coordinate (`Cube.KernelOp.isForm_foldSlicewise`). This replaces
multidimensional Fubini arguments in the construction of tensor approximants.

If `T` reproduces its functions, `T φ_j = φ_j` (`Cube.KernelOp.Reproduces`), then the bounded
measurable functions with the form of `T` in every coordinate are exactly the combinations of the
tensor products `∏_i φ_{j_i}(x_i)` (`Cube.KernelOp.mem_span_prod_of_isForm`,
`Cube.KernelOp.isForm_of_mem_span_prod`). The proof expands the coefficients one coordinate at a
time (`Cube.KernelOp.partialTensor_subset_span`): a form in coordinate `i` is reproduced by
`T^{(i)}` (`Cube.KernelOp.IsForm.slicewise_self`), which writes its coefficient as a combination of
the `φ_j(x_i)`.

On `L_p(Q)` the slicewise action inherits the bounds of `T` on `L_p[0, 1]` slice by slice
(`Cube.KernelOp.eLpNorm_slicewise_le`), and the slices of `f - T^{(i)} f` are the errors of `T` on
the slices of `f` (`Cube.slice_sub_slicewise`). By linearity, the error of the action in all
coordinates telescopes into the errors in the single coordinates
(`Cube.KernelOp.eLpNorm_sub_foldSlicewise_le`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Cube

open Interval

/-- A function is **bounded and measurable**. -/
def BddMeas {α : Type*} [MeasurableSpace α] (g : α → ℂ) : Prop :=
  Measurable g ∧ ∃ M : ℝ, ∀ x, ‖g x‖ ≤ M

/-- Bounded measurable functions are closed under sums. -/
theorem BddMeas.add {α : Type*} [MeasurableSpace α] {f g : α → ℂ} (hf : BddMeas f)
    (hg : BddMeas g) : BddMeas (f + g) := by
  obtain ⟨hfm, M, hM⟩ := hf
  obtain ⟨hgm, N, hN⟩ := hg
  exact ⟨hfm.add hgm, M + N, fun x => (norm_add_le _ _).trans (add_le_add (hM x) (hN x))⟩

/-- Bounded measurable functions are closed under constant multiples. -/
theorem BddMeas.const_mul {α : Type*} [MeasurableSpace α] {f : α → ℂ} (hf : BddMeas f) (c : ℂ) :
    BddMeas (fun x => c * f x) := by
  obtain ⟨hfm, M, hM⟩ := hf
  exact ⟨measurable_const.mul hfm, ‖c‖ * M, fun x => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hM x) (norm_nonneg c)⟩

/-- The zero function is bounded and measurable. -/
theorem bddMeas_zero {α : Type*} [MeasurableSpace α] : BddMeas (0 : α → ℂ) :=
  ⟨measurable_const, 0, fun _ => by simp⟩

/-- Finite sums of bounded measurable functions are bounded and measurable. -/
theorem bddMeas_sum {α ι : Type*} [MeasurableSpace α] (s : Finset ι) {f : ι → α → ℂ}
    (hf : ∀ j ∈ s, BddMeas (f j)) : BddMeas (fun x => ∑ j ∈ s, f j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨measurable_const, 0, fun _ => by simp⟩
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (hf j (Finset.mem_insert_self j s)).add (ih fun j' hj' => hf j'
      (Finset.mem_insert_of_mem hj'))

/-- Products `∏_{i ∈ s} u_i(x_i)` of bounded measurable functions of single coordinates are
bounded and measurable. -/
theorem bddMeas_prod_coord {d : ℕ} (s : Finset (Fin d)) {u : Fin d → ℝ → ℂ}
    (hu : ∀ i ∈ s, BddMeas (u i)) : BddMeas (fun x : Fin d → ℝ => ∏ i ∈ s, u i (x i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨measurable_const, 1, fun _ => by simp⟩
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    obtain ⟨hm, M, hM⟩ := hu a (Finset.mem_insert_self a s)
    obtain ⟨hm', M', hM'⟩ := ih fun i hi => hu i (Finset.mem_insert_of_mem hi)
    refine ⟨(hm.comp (measurable_pi_apply a)).mul hm', M * M', fun x => ?_⟩
    rw [norm_mul]
    exact mul_le_mul (hM (x a)) (hM' x) (norm_nonneg _) ((norm_nonneg (u a (x a))).trans (hM (x a)))

/-- A bounded measurable function is integrable on `[0, 1]`. -/
theorem BddMeas.integrableOn_Icc {g : ℝ → ℂ} (hg : BddMeas g) :
    IntegrableOn g (Icc (0 : ℝ) 1) := by
  obtain ⟨hgm, M, hM⟩ := hg
  exact IntegrableOn.of_bound (by simp) hgm.aestronglyMeasurable M
    (Filter.Eventually.of_forall hM)

/-- A bounded measurable function lies in every `L_p` of a finite measure. -/
theorem BddMeas.memLp {α : Type*} [MeasurableSpace α] {g : α → ℂ} (hg : BddMeas g)
    (p : ℝ≥0∞) (μ : Measure α) [IsFiniteMeasure μ] : MemLp g p μ := by
  obtain ⟨hgm, M, hM⟩ := hg
  exact MemLp.of_bound hgm.aestronglyMeasurable M (Filter.Eventually.of_forall hM)

/-- The slices of a bounded measurable function are bounded and measurable. -/
theorem BddMeas.slice {d : ℕ} {g : (Fin d → ℝ) → ℂ} (hg : BddMeas g) (x : Fin d → ℝ)
    (i : Fin d) : BddMeas (slice g x i) := by
  obtain ⟨hgm, M, hM⟩ := hg
  exact ⟨measurable_slice hgm x i, M, fun _ => hM _⟩

/-- A **finite-rank kernel operator** on functions on `[0, 1]`: `T g = ∑_j (∫_0^1 g κ_j) φ_j`
with bounded measurable kernels `κ_j` and functions `φ_j`. -/
structure KernelOp (ι : Type*) [Fintype ι] where
  /-- The kernels of the coefficients. -/
  kernel : ι → ℝ → ℂ
  /-- The functions of the range. -/
  rangeFn : ι → ℝ → ℂ
  bddMeas_kernel : ∀ j, BddMeas (kernel j)
  bddMeas_rangeFn : ∀ j, BddMeas (rangeFn j)

namespace KernelOp

variable {ι : Type*} [Fintype ι] (T : KernelOp ι)

/-- The coefficient `∫_0^1 g κ_j`. -/
noncomputable def coef (g : ℝ → ℂ) (j : ι) : ℂ := ∫ s in Icc (0 : ℝ) 1, g s * T.kernel j s

/-- The operator `T g = ∑_j (∫_0^1 g κ_j) φ_j`. -/
noncomputable def apply (g : ℝ → ℂ) (t : ℝ) : ℂ := ∑ j, T.coef g j * T.rangeFn j t

/-- The products `g κ_j` of a function `g` integrable on `[0, 1]` are integrable on `[0, 1]`. -/
theorem integrableOn_mul_kernel {g : ℝ → ℂ} (hg : IntegrableOn g (Icc (0 : ℝ) 1)) (j : ι) :
    IntegrableOn (fun s => g s * T.kernel j s) (Icc (0 : ℝ) 1) :=
  hg.mul_bdd (c := (T.bddMeas_kernel j).2.choose) (T.bddMeas_kernel j).1.aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => (T.bddMeas_kernel j).2.choose_spec s)

/-- The coefficients are additive on functions integrable on `[0, 1]`. -/
theorem coef_add {g h : ℝ → ℂ} (hg : IntegrableOn g (Icc (0 : ℝ) 1))
    (hh : IntegrableOn h (Icc (0 : ℝ) 1)) (j : ι) :
    T.coef (fun s => g s + h s) j = T.coef g j + T.coef h j := by
  simp only [coef, add_mul]
  exact integral_add (T.integrableOn_mul_kernel hg j) (T.integrableOn_mul_kernel hh j)

/-- The coefficients of a difference of functions integrable on `[0, 1]`. -/
theorem coef_sub {g h : ℝ → ℂ} (hg : IntegrableOn g (Icc (0 : ℝ) 1))
    (hh : IntegrableOn h (Icc (0 : ℝ) 1)) (j : ι) :
    T.coef (fun s => g s - h s) j = T.coef g j - T.coef h j := by
  simp only [coef, sub_mul]
  exact integral_sub (T.integrableOn_mul_kernel hg j) (T.integrableOn_mul_kernel hh j)

/-- The coefficients are homogeneous. -/
theorem coef_const_mul (c : ℂ) (g : ℝ → ℂ) (j : ι) :
    T.coef (fun s => c * g s) j = c * T.coef g j := by
  simp only [coef, mul_assoc]
  exact integral_const_mul c _

/-- The coefficients of finite sums of functions integrable on `[0, 1]`. -/
theorem coef_sum {κι : Type*} (s : Finset κι) {g : κι → ℝ → ℂ}
    (hg : ∀ a ∈ s, IntegrableOn (g a) (Icc (0 : ℝ) 1)) (j : ι) :
    T.coef (fun t => ∑ a ∈ s, g a t) j = ∑ a ∈ s, T.coef (g a) j := by
  simp only [coef, Finset.sum_mul]
  exact integral_finsetSum _ fun a ha => T.integrableOn_mul_kernel (hg a ha) j

/-- **Kernel operators are linear** on functions integrable on `[0, 1]`:
`T(g - h) = T g - T h`. -/
theorem apply_sub {g h : ℝ → ℂ} (hg : IntegrableOn g (Icc (0 : ℝ) 1))
    (hh : IntegrableOn h (Icc (0 : ℝ) 1)) (t : ℝ) :
    T.apply (fun s => g s - h s) t = T.apply g t - T.apply h t := by
  simp only [apply, T.coef_sub hg hh, sub_mul, Finset.sum_sub_distrib]

/-- `|∫_0^1 g κ_j| ≤ M B` for `|g| ≤ M` and `|κ_j| ≤ B`. -/
theorem norm_coef_le {g : ℝ → ℂ} {M : ℝ} (hM : ∀ s, ‖g s‖ ≤ M) (j : ι) :
    ‖T.coef g j‖ ≤ M * (T.bddMeas_kernel j).2.choose := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (0 : ℝ) 1)
    (f := fun s => g s * T.kernel j s) (C := M * (T.bddMeas_kernel j).2.choose) (by simp) fun s
      _ => by
      rw [norm_mul]
      exact mul_le_mul (hM s) ((T.bddMeas_kernel j).2.choose_spec s) (norm_nonneg _)
        ((norm_nonneg _).trans (hM s))
  rw [coef]
  simpa [Real.volume_real_Icc] using h

/-! ### The slicewise action -/

variable {d : ℕ}

/-- The **slicewise action in coordinate `i`**: `T^{(i)} g(x) = T(slice g x i)(x_i)`. -/
noncomputable def slicewise (i : Fin d) (g : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  T.apply (slice g x i) (x i)

/-- The slicewise action as a sum: `T^{(i)} g(x) = ∑_j (∫_0^1 g(x with s in place i) κ_j(s) ds)
φ_j(x_i)`. -/
theorem slicewise_eq (i : Fin d) (g : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    T.slicewise i g x = ∑ j, T.coef (slice g x i) j * T.rangeFn j (x i) := rfl

/-- The slices of `T^{(i)} g` in coordinate `i` are the images of the slices under `T`. -/
theorem slice_slicewise (i : Fin d) (g : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    slice (T.slicewise i g) x i = T.apply (slice g x i) := by
  funext t
  simp only [slice, slicewise]
  rw [slice_update, Function.update_self]

/-- The coefficients of the slices are measurable in the point. -/
theorem measurable_coef_slice {g : (Fin d → ℝ) → ℂ} (hg : Measurable g) (i : Fin d) (j : ι) :
    Measurable fun x => T.coef (slice g x i) j := by
  have h : StronglyMeasurable (Function.uncurry fun (x : Fin d → ℝ) (s : ℝ) =>
      slice g x i s * T.kernel j s) :=
    ((measurable_slice_uncurry hg i).mul ((T.bddMeas_kernel j).1.comp
      measurable_snd)).stronglyMeasurable
  exact (h.integral_prod_right (ν := volume.restrict (Icc (0 : ℝ) 1))).measurable

/-- The slicewise action of a measurable function is measurable. -/
theorem measurable_slicewise {g : (Fin d → ℝ) → ℂ} (hg : Measurable g) (i : Fin d) :
    Measurable (T.slicewise i g) :=
  Finset.measurable_sum _ fun j _ => (T.measurable_coef_slice hg i j).mul
    ((T.bddMeas_rangeFn j).1.comp (measurable_pi_apply i))

/-- The slicewise action keeps functions bounded and measurable. -/
theorem bddMeas_slicewise {g : (Fin d → ℝ) → ℂ} (hg : BddMeas g) (i : Fin d) :
    BddMeas (T.slicewise i g) := by
  obtain ⟨hgm, M, hM⟩ := hg
  refine ⟨T.measurable_slicewise hgm i, ∑ j, M * (T.bddMeas_kernel j).2.choose *
      (T.bddMeas_rangeFn j).2.choose, fun x => ?_⟩
  rw [slicewise_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  exact mul_le_mul (T.norm_coef_le (g := slice g x i) (fun s => hM _) j)
    ((T.bddMeas_rangeFn j).2.choose_spec _) (norm_nonneg _)
    ((norm_nonneg _).trans (T.norm_coef_le (g := slice g x i) (fun s => hM _) j))

/-- **The slicewise action is linear** on bounded measurable functions. -/
theorem slicewise_sub {g h : (Fin d → ℝ) → ℂ} (hg : BddMeas g) (hh : BddMeas h) (i : Fin d)
    (x : Fin d → ℝ) :
    T.slicewise i (fun y => g y - h y) x = T.slicewise i g x - T.slicewise i h x :=
  T.apply_sub (hg.slice x i).integrableOn_Icc (hh.slice x i).integrableOn_Icc (x i)

/-! ### The form of an operator in a coordinate -/

/-- `g` has the **form of `T` in coordinate `i`**: `g(x) = ∑_j c_j(x) φ_j(x_i)` with bounded
measurable coefficients `c_j` that do not depend on `x_i`. -/
def IsForm (i : Fin d) (g : (Fin d → ℝ) → ℂ) : Prop :=
  ∃ c : ι → (Fin d → ℝ) → ℂ, (∀ j, BddMeas (c j)) ∧
    (∀ j x t, c j (Function.update x i t) = c j x) ∧ ∀ x, g x = ∑ j, c j x * T.rangeFn j (x i)

/-- **The slicewise action produces the form**: `T^{(i)} g` has the form of `T` in coordinate `i`
for bounded measurable `g`, with the coefficients `c_j(x) = ∫_0^1 g(x with s in place i) κ_j`. -/
theorem isForm_slicewise {g : (Fin d → ℝ) → ℂ} (hg : BddMeas g) (i : Fin d) :
    T.IsForm i (T.slicewise i g) := by
  obtain ⟨hgm, M, hM⟩ := hg
  refine ⟨fun j x => T.coef (slice g x i) j, fun j => ⟨T.measurable_coef_slice hgm i j,
    M * (T.bddMeas_kernel j).2.choose, fun x => T.norm_coef_le (g := slice g x i) (fun s => hM
      _) j⟩,
    fun j x t => by simp only [slice_update], fun x => rfl⟩

/-- The slices of a function of the form of `T` in coordinate `i` are combinations of the `φ_j`. -/
theorem IsForm.slice_eq {i : Fin d} {g : (Fin d → ℝ) → ℂ} (hg : T.IsForm i g)
    (x : Fin d → ℝ) : ∃ a : ι → ℂ, slice g x i = fun t => ∑ j, a j * T.rangeFn j t := by
  obtain ⟨c, -, hci, hgc⟩ := hg
  refine ⟨fun j => c j x, funext fun t => ?_⟩
  simp only [slice, hgc, hci, Function.update_self]

/-- **The form is kept by the action in another coordinate**: if `g` has the form of `T` in
coordinate `i` and `j ≠ i`, then `S^{(j)} g` has the form of `T` in coordinate `i`, with the
coefficients `S^{(j)} c_a`. -/
theorem IsForm.slicewise {κι : Type*} [Fintype κι] (S : KernelOp κι) {i j : Fin d} (hij : i ≠ j)
    {g : (Fin d → ℝ) → ℂ} (hg : T.IsForm i g) : T.IsForm i (S.slicewise j g) := by
  obtain ⟨c, hcb, hci, hgc⟩ := hg
  refine ⟨fun a => S.slicewise j (c a), fun a => S.bddMeas_slicewise (hcb a) j,
    fun a x t => ?_, fun x => ?_⟩
  · have hs : slice (c a) (Function.update x i t) j = slice (c a) x j := by
      funext s
      simp only [slice]
      rw [Function.update_comm hij, hci]
    simp only [KernelOp.slicewise, hs, Function.update_of_ne hij.symm]
  · have hslice : slice g x j = fun s => ∑ a, c a (Function.update x j s) * T.rangeFn a (x i) := by
      funext s
      simp only [slice, hgc, Function.update_of_ne hij]
    rw [KernelOp.slicewise_eq, hslice]
    have hcoef : ∀ b, S.coef (fun s => ∑ a, c a (Function.update x j s) * T.rangeFn a (x i)) b =
        ∑ a, S.coef (fun s => c a (Function.update x j s)) b * T.rangeFn a (x i) := fun b => by
      have hb : ∀ a ∈ (Finset.univ : Finset ι),
          BddMeas (fun s => c a (Function.update x j s) * T.rangeFn a (x i)) := fun a _ => by
        obtain ⟨hcm, M, hM⟩ := hcb a
        exact ⟨(hcm.comp (measurable_update x)).mul measurable_const, M * ‖T.rangeFn a (x i)‖,
          fun s => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)⟩
      rw [S.coef_sum _ fun a ha => (hb a ha).integrableOn_Icc]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [mul_comm _ (T.rangeFn a (x i))]
      rw [S.coef_const_mul]
    simp only [hcoef, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [KernelOp.slicewise_eq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [show slice (c a) x j = fun s => c a (Function.update x j s) from rfl]
    ring

/-- Functions of the form of `T` in a coordinate form a linear space: sums. -/
theorem IsForm.add {i : Fin d} {f g : (Fin d → ℝ) → ℂ} (hf : T.IsForm i f) (hg : T.IsForm i g) :
    T.IsForm i (f + g) := by
  obtain ⟨c, hcb, hci, hfc⟩ := hf
  obtain ⟨c', hcb', hci', hgc⟩ := hg
  refine ⟨fun j => c j + c' j, fun j => (hcb j).add (hcb' j), fun j x t => by
    simp only [Pi.add_apply, hci, hci'], fun x => ?_⟩
  simp only [Pi.add_apply, hfc, hgc, add_mul, Finset.sum_add_distrib]

/-- Functions of the form of `T` in a coordinate form a linear space: constant multiples. -/
theorem IsForm.const_mul {i : Fin d} {g : (Fin d → ℝ) → ℂ} (hg : T.IsForm i g) (a : ℂ) :
    T.IsForm i (fun x => a * g x) := by
  obtain ⟨c, hcb, hci, hgc⟩ := hg
  refine ⟨fun j x => a * c j x, fun j => (hcb j).const_mul a, fun j x t => by
    simp only [hci], fun x => ?_⟩
  simp only [hgc, Finset.mul_sum, mul_assoc]

/-- The zero function has the form of every operator. -/
theorem isForm_zero (i : Fin d) : T.IsForm i 0 :=
  ⟨fun _ => 0, fun _ => bddMeas_zero, fun _ _ _ => rfl, fun _ => by simp⟩

/-- Functions equal everywhere have the same forms. -/
theorem IsForm.congr {i : Fin d} {f g : (Fin d → ℝ) → ℂ} (hf : T.IsForm i f) (hfg : f = g) :
    T.IsForm i g := hfg ▸ hf

/-- **Refinement of forms**: if every `φ_j` of `T` is a combination of the `φ'_{j'}` of `T'`,
then the form of `T` in a coordinate is a form of `T'`. -/
theorem IsForm.refine {κι : Type*} [Fintype κι] {T' : KernelOp κι} {i : Fin d}
    {g : (Fin d → ℝ) → ℂ} (hg : T.IsForm i g) (M : ι → κι → ℂ)
    (hM : ∀ j t, T.rangeFn j t = ∑ j', M j j' * T'.rangeFn j' t) : T'.IsForm i g := by
  obtain ⟨c, hcb, hci, hgc⟩ := hg
  refine ⟨fun j' x => ∑ j, M j j' * c j x, fun j' => bddMeas_sum _ fun j _ =>
    (hcb j).const_mul _, fun j' x t => by simp only [hci], fun x => ?_⟩
  rw [hgc]
  simp only [hM, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ### Tensor products -/

/-- A kernel operator **reproduces its functions** if `T φ_m = φ_m` for every `m`. -/
def Reproduces : Prop := ∀ m, T.apply (T.rangeFn m) = T.rangeFn m

/-- A reproducing operator is the identity on the combinations of its functions. -/
theorem Reproduces.apply_sum (hT : T.Reproduces) (a : ι → ℂ) (t : ℝ) :
    T.apply (fun s => ∑ m, a m * T.rangeFn m s) t = ∑ m, a m * T.rangeFn m t := by
  have hcoef : ∀ j, T.coef (fun s => ∑ m, a m * T.rangeFn m s) j =
      ∑ m, a m * T.coef (T.rangeFn m) j := fun j => by
    rw [T.coef_sum (g := fun m s => a m * T.rangeFn m s) _
      fun m _ => ((T.bddMeas_rangeFn m).const_mul (a m)).integrableOn_Icc]
    exact Finset.sum_congr rfl fun m _ => T.coef_const_mul _ _ _
  simp only [apply, hcoef, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h := congrFun (hT m) t
  simp only [apply] at h
  rw [← h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **A reproducing operator acts as the identity on its forms**: `T^{(i)} g = g` if `g` has
the form of `T` in coordinate `i`. -/
theorem IsForm.slicewise_self (hT : T.Reproduces) {i : Fin d} {g : (Fin d → ℝ) → ℂ}
    (hg : T.IsForm i g) : T.slicewise i g = g := by
  funext x
  obtain ⟨a, ha⟩ := KernelOp.IsForm.slice_eq T hg x
  rw [KernelOp.slicewise, ha, KernelOp.Reproduces.apply_sum T hT a (x i)]
  have h := congrFun ha (x i)
  simp only [slice, Function.update_eq_self] at h
  exact h.symm

/-- **The coefficients of slices keep the forms in other coordinates**: if `g` has the form of
`T` in coordinate `i` and `j ≠ i`, then `x ↦ ∫_0^1 g(x with s in place j) κ'_m(s) ds` has the
form of `T` in coordinate `i`. -/
theorem IsForm.coef_slice {κι : Type*} [Fintype κι] (S : KernelOp κι) {i j : Fin d}
    (hij : i ≠ j) {g : (Fin d → ℝ) → ℂ} (hg : T.IsForm i g) (m : κι) :
    T.IsForm i (fun x => S.coef (slice g x j) m) := by
  obtain ⟨c, hcb, hci, hgc⟩ := hg
  refine ⟨fun a x => S.coef (slice (c a) x j) m, fun a => ?_, fun a x t => ?_, fun x => ?_⟩
  · obtain ⟨hcm, M, hM⟩ := hcb a
    exact ⟨S.measurable_coef_slice hcm j m, M * (S.bddMeas_kernel m).2.choose,
      fun x => S.norm_coef_le (g := slice (c a) x j) (fun s => hM _) m⟩
  · have hs : slice (c a) (Function.update x i t) j = slice (c a) x j := by
      funext s
      simp only [slice]
      rw [Function.update_comm hij, hci]
    simp only [hs]
  · change S.coef (slice g x j) m = ∑ a, S.coef (slice (c a) x j) m * T.rangeFn a (x i)
    have hslice : slice g x j = fun s => ∑ a, c a (Function.update x j s) * T.rangeFn a (x i) := by
      funext s
      simp only [slice, hgc, Function.update_of_ne hij]
    rw [hslice]
    have hb : ∀ a ∈ (Finset.univ : Finset ι), IntegrableOn
        (fun s => c a (Function.update x j s) * T.rangeFn a (x i)) (Icc (0 : ℝ) 1) := fun a _ => by
      obtain ⟨hcm, M, hM⟩ := hcb a
      exact BddMeas.integrableOn_Icc ⟨(hcm.comp (measurable_update x)).mul measurable_const,
        M * ‖T.rangeFn a (x i)‖, fun s => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)⟩
    rw [S.coef_sum (g := fun a s => c a (Function.update x j s) * T.rangeFn a (x i)) _ hb]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [mul_comm _ (T.rangeFn a (x i))]
    rw [S.coef_const_mul]
    rfl

/-- The **partial tensor products** for a set `S` of coordinates: `c(x) ∏_{i ∈ S} φ_{j_i}(x_i)`
with `c` bounded and measurable, independent of the coordinates in `S`, and with the form of `T`
in every coordinate outside `S`. -/
def partialTensor (S : Finset (Fin d)) : Set ((Fin d → ℝ) → ℂ) :=
  {G | ∃ (c : (Fin d → ℝ) → ℂ) (j : Fin d → ι), BddMeas c ∧
    (∀ x, ∀ i ∈ S, ∀ t, c (Function.update x i t) = c x) ∧ (∀ i ∉ S, T.IsForm i c) ∧
    G = fun x => c x * ∏ i ∈ S, T.rangeFn (j i) (x i)}

/-- **One more coordinate**: for a reproducing operator, every partial tensor product for `S` is a
combination of partial tensor products for `S ∪ {i₀}`, by expanding its coefficient in
coordinate `i₀`. -/
theorem partialTensor_subset_span (hT : T.Reproduces) {S : Finset (Fin d)} {i₀ : Fin d}
    (hi₀ : i₀ ∉ S) : T.partialTensor S ⊆ Submodule.span ℂ (T.partialTensor (insert i₀ S)) := by
  classical
  rintro G ⟨c, j, hcb, hci, hcf, rfl⟩
  have hc : ∀ x, c x = ∑ m, T.coef (slice c x i₀) m * T.rangeFn m (x i₀) := fun x =>
    (congrFun (KernelOp.IsForm.slicewise_self T hT (hcf i₀ hi₀)) x).symm
  have hG : (fun x => c x * ∏ i ∈ S, T.rangeFn (j i) (x i)) = ∑ m, fun x =>
      T.coef (slice c x i₀) m *
        ∏ i ∈ insert i₀ S, T.rangeFn (Function.update j i₀ m i) (x i) := by
    funext x
    rw [Finset.sum_apply, hc x, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.prod_insert hi₀, Function.update_self]
    have hprod : ∏ i ∈ S, T.rangeFn (Function.update j i₀ m i) (x i) =
        ∏ i ∈ S, T.rangeFn (j i) (x i) :=
      Finset.prod_congr rfl fun i hi => by
        rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hi₀)]
    rw [hprod]
    ring
  rw [hG]
  refine Submodule.sum_mem _ fun m _ => Submodule.subset_span
    ⟨fun x => T.coef (slice c x i₀) m, Function.update j i₀ m, ?_, ?_, ?_, rfl⟩
  · obtain ⟨hcm, M, hM⟩ := hcb
    exact ⟨T.measurable_coef_slice hcm i₀ m, M * (T.bddMeas_kernel m).2.choose,
      fun x => T.norm_coef_le (g := slice c x i₀) (fun s => hM _) m⟩
  · intro x i hi t
    rcases Finset.mem_insert.1 hi with rfl | hi'
    · simp only [slice_update]
    · have hs : slice c (Function.update x i t) i₀ = slice c x i₀ := by
        funext s
        simp only [slice]
        rw [Function.update_comm (ne_of_mem_of_not_mem hi' hi₀), hci _ i hi']
      simp only [hs]
  · intro i hi
    have hi' : i ∉ S := fun h => hi (Finset.mem_insert_of_mem h)
    have hne : i ≠ i₀ := fun h => hi (h ▸ Finset.mem_insert_self i₀ S)
    exact KernelOp.IsForm.coef_slice T T hne (hcf i hi') m

/-- **Forms in every coordinate are tensor products**: for a reproducing operator, a bounded
measurable function with the form of `T` in every coordinate is a combination of the products
`∏_i φ_{j_i}(x_i)`. -/
theorem mem_span_prod_of_isForm [Nonempty ι] (hT : T.Reproduces) {g : (Fin d → ℝ) → ℂ}
    (hg : BddMeas g) (hform : ∀ i, T.IsForm i g) :
    g ∈ Submodule.span ℂ
      (Set.range fun j : Fin d → ι => fun x => ∏ i, T.rangeFn (j i) (x i)) := by
  classical
  have hS : ∀ S : Finset (Fin d), g ∈ Submodule.span ℂ (T.partialTensor S) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine Submodule.subset_span ⟨g, fun _ => Classical.arbitrary ι, hg,
        fun x i hi => absurd hi (Finset.notMem_empty i), fun i _ => hform i, ?_⟩
      funext x
      simp
    | insert a S ha ih => exact Submodule.span_le.2 (T.partialTensor_subset_span hT ha) ih
  refine Submodule.span_le.2 ?_ (hS Finset.univ)
  rintro G ⟨c, j, -, hci, -, rfl⟩
  have hconst : ∀ x, c x = c 0 := fun x => by
    have key : ∀ S : Finset (Fin d), c (S.piecewise 0 x) = c x := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp
      | insert a S ha ih => rw [Finset.piecewise_insert, hci _ a (Finset.mem_univ a), ih]
    have h := key Finset.univ
    rw [Finset.piecewise_univ] at h
    exact h.symm
  have hG : (fun x => c x * ∏ i ∈ Finset.univ, T.rangeFn (j i) (x i)) =
      c 0 • fun x => ∏ i, T.rangeFn (j i) (x i) := by
    funext x
    rw [hconst x]
    rfl
  rw [hG]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- Products `∏_l φ_{j_l}(x_l)` have the form of `T` in every coordinate. -/
theorem isForm_prod (j : Fin d → ι) (i : Fin d) :
    T.IsForm i (fun x => ∏ l, T.rangeFn (j l) (x l)) := by
  classical
  refine ⟨fun m => if m = j i then (fun x => ∏ l ∈ Finset.univ.erase i, T.rangeFn (j l) (x l))
    else 0, fun m => ?_, fun m x t => ?_, fun x => ?_⟩
  · dsimp only
    split_ifs
    · exact bddMeas_prod_coord _ fun l _ => T.bddMeas_rangeFn (j l)
    · exact bddMeas_zero
  · dsimp only
    split_ifs
    · exact Finset.prod_congr rfl fun l hl => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
    · rfl
  · rw [Finset.sum_eq_single (j i) (fun m _ hm => by simp [hm])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp only [↓reduceIte]
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i)]

/-- **Tensor products have the forms**: combinations of products `∏_i φ_{j_i}(x_i)` are bounded
and measurable and have the form of `T` in every coordinate. -/
theorem isForm_of_mem_span_prod {g : (Fin d → ℝ) → ℂ}
    (hg : g ∈ Submodule.span ℂ
      (Set.range fun j : Fin d → ι => fun x => ∏ i, T.rangeFn (j i) (x i))) :
    BddMeas g ∧ ∀ i, T.IsForm i g := by
  induction hg using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨j, rfl⟩ := hG
    exact ⟨bddMeas_prod_coord _ fun l _ => T.bddMeas_rangeFn (j l), fun i => T.isForm_prod j i⟩
  | zero => exact ⟨bddMeas_zero, fun i => T.isForm_zero i⟩
  | add f g _ _ hf hg => exact ⟨hf.1.add hg.1, fun i => (hf.2 i).add _ (hg.2 i)⟩
  | smul a f _ hf => exact ⟨hf.1.const_mul a, fun i => (hf.2 i).const_mul _ a⟩

/-! ### Action in all coordinates -/

/-- The action of `T` in the coordinates of a list, the last coordinate first:
`T^{(l_1)} ∘ ⋯ ∘ T^{(l_m)}`. -/
noncomputable def foldSlicewise (l : List (Fin d)) (g : (Fin d → ℝ) → ℂ) :
    (Fin d → ℝ) → ℂ :=
  l.foldr (fun i acc => T.slicewise i acc) g

/-- The action in the coordinates of the empty list is the identity. -/
theorem foldSlicewise_nil (g : (Fin d → ℝ) → ℂ) : T.foldSlicewise [] g = g := rfl

/-- The action in the coordinates of `i :: l` is `T^{(i)}` after the action in those of `l`. -/
theorem foldSlicewise_cons (i : Fin d) (l : List (Fin d)) (g : (Fin d → ℝ) → ℂ) :
    T.foldSlicewise (i :: l) g = T.slicewise i (T.foldSlicewise l g) := rfl

/-- The action in the coordinates of a list keeps functions bounded and measurable. -/
theorem bddMeas_foldSlicewise (l : List (Fin d)) {g : (Fin d → ℝ) → ℂ} (hg : BddMeas g) :
    BddMeas (T.foldSlicewise l g) := by
  induction l with
  | nil => exact hg
  | cons i l ih => exact T.bddMeas_slicewise ih i

/-- **The action in all coordinates of a list gives the form in each of them.** -/
theorem isForm_foldSlicewise (l : List (Fin d)) {g : (Fin d → ℝ) → ℂ} (hg : BddMeas g)
    {i : Fin d} (hi : i ∈ l) : T.IsForm i (T.foldSlicewise l g) := by
  induction l with
  | nil => exact absurd hi List.not_mem_nil
  | cons j l ih =>
    rcases eq_or_ne i j with rfl | hij
    · exact T.isForm_slicewise (T.bddMeas_foldSlicewise l hg) i
    · exact KernelOp.IsForm.slicewise T T hij (ih ((List.mem_cons.1 hi).resolve_left hij))

/-! ### Bounds in `L_p` of the cube -/

/-- **Slicewise bounds**: if `‖T u‖_{L_p[0,1]} ≤ C ‖u‖_{L_p[0,1]}` for all measurable `u`, then
`‖T^{(i)} g‖_{L_p(Q)} ≤ C ‖g‖_{L_p(Q)}` for measurable `g` with measurable `T^{(i)} g`. -/
theorem eLpNorm_slicewise_le {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) {C : ℝ≥0∞}
    (hT : ∀ u : ℝ → ℂ, Measurable u → eLpNorm (T.apply u) p unitVol ≤ C * eLpNorm u p unitVol)
    (i : Fin d) {g : (Fin d → ℝ) → ℂ} (hg : Measurable g)
    (hTg : Measurable (T.slicewise i g)) :
    eLpNorm (T.slicewise i g) p (cubeVol d) ≤ C * eLpNorm g p (cubeVol d) :=
  eLpNorm_cubeVol_le_of_slice_le hTg hg hp0 hp i fun x => by
    rw [slice_slicewise]
    exact hT _ (measurable_slice hg x i)

/-- **Telescoping over the coordinates of a list**: if `‖T u‖_{L_p[0,1]} ≤ C ‖u‖_{L_p[0,1]}`,
then `‖g - T^{(l_1)} ⋯ T^{(l_m)} g‖_{L_p(Q)} ≤ (1 + C)^m ∑_{i ∈ l} ‖g - T^{(i)} g‖_{L_p(Q)}` for
bounded measurable `g`. The step is `g - T^{(i)} h = (g - T^{(i)} g) + T^{(i)} (g - h)`. -/
theorem eLpNorm_sub_foldSlicewise_le {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) {C : ℝ≥0∞}
    (hT : ∀ u : ℝ → ℂ, Measurable u → eLpNorm (T.apply u) p unitVol ≤ C * eLpNorm u p unitVol)
    (l : List (Fin d)) {g : (Fin d → ℝ) → ℂ} (hg : BddMeas g) :
    eLpNorm (fun x => g x - T.foldSlicewise l g x) p (cubeVol d) ≤
      (1 + C) ^ l.length *
        (l.map fun i => eLpNorm (fun x => g x - T.slicewise i g x) p (cubeVol d)).sum := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  induction l with
  | nil => simp [foldSlicewise_nil]
  | cons i l ih =>
    have hF := T.bddMeas_foldSlicewise l hg
    have hgF : Measurable fun y => g y - T.foldSlicewise l g y := hg.1.sub hF.1
    have heq : (fun x => g x - T.foldSlicewise (i :: l) g x) =
        (fun x => g x - T.slicewise i g x) +
          T.slicewise i (fun y => g y - T.foldSlicewise l g y) := by
      funext x
      rw [Pi.add_apply, foldSlicewise_cons, T.slicewise_sub hg hF i x]
      ring
    have h2 : eLpNorm (T.slicewise i fun y => g y - T.foldSlicewise l g y) p (cubeVol d) ≤
        C * eLpNorm (fun y => g y - T.foldSlicewise l g y) p (cubeVol d) :=
      T.eLpNorm_slicewise_le hp0 hp' hT i hgF (T.measurable_slicewise hgF i)
    set e := eLpNorm (fun x => g x - T.slicewise i g x) p (cubeVol d)
    set S := (l.map fun i => eLpNorm (fun x => g x - T.slicewise i g x) p (cubeVol d)).sum
    have h1 : 1 ≤ (1 + C) ^ (l.length + 1) := one_le_pow₀ le_self_add
    rw [heq, List.length_cons, List.map_cons, List.sum_cons]
    calc eLpNorm ((fun x => g x - T.slicewise i g x) +
          T.slicewise i (fun y => g y - T.foldSlicewise l g y)) p (cubeVol d)
        ≤ e + C * ((1 + C) ^ l.length * S) :=
          (eLpNorm_add_le hp).trans (add_le_add le_rfl (h2.trans (mul_le_mul' le_rfl ih)))
      _ = e + (1 + C) ^ l.length * C * S := by ring
      _ ≤ (1 + C) ^ (l.length + 1) * e + (1 + C) ^ l.length * (1 + C) * S := by
          gcongr
          · exact le_mul_of_one_le_left' h1
          · exact le_add_self
      _ = (1 + C) ^ (l.length + 1) * (e + S) := by ring

end KernelOp

/-- The slices of `f - T^{(i)} f` in coordinate `i` are the errors of `T` on the slices of `f`. -/
theorem slice_sub_slicewise {d : ℕ} {ι : Type*} [Fintype ι] (T : KernelOp ι)
    (f : (Fin d → ℝ) → ℂ) (i : Fin d) (x : Fin d → ℝ) :
    slice (fun y => f y - T.slicewise i f y) x i =
      fun t => slice f x i t - T.apply (slice f x i) t := by
  funext t
  rw [← KernelOp.slice_slicewise]
  rfl

end Cube
