/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.FieldSpaces
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Truncation.WeakGradientLimit
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.Algebra.H10Function

/-!
# ZeroExtension

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: extension by zero across an inclusion of domains

This file supplies the analytic ingredient needed to *glue* competitors in the
variational subadditivity argument of ABK26, `l.subadd.betterer`: if `V ⊆ U`
then the extension by zero of an element of `H¹₀(V)` is an element of
`H¹₀(U)`, hence

* `L²_{pot,0}(V) ∋ f ↦ 1_V f ∈ L²_{pot,0}(U)`, and
* `L²_{sol,0}(V) ∋ g ↦ 1_V g ∈ L²_{sol,0}(U)`.

The `L²_{pot,0}` half is the substantial one: the approximating sequence of an
`H¹₀(V)` element consists of smooth functions with `tsupport ⊆ V ⊆ U`, so it is
also an admissible approximating sequence in `U`, and CoarseGraining's
`L²`-closedness of weak gradients (`HasWeakGradientOn.of_tendsto_eLpNorm_two`)
identifies the weak gradient of the extension as the extension of the weak
gradient.  The `L²_{sol,0}` half is elementary: an `H¹(U)` test function
restricts to an `H¹(V)` test function with the same gradient.

Everything is stated for CoarseGraining's a.e.-robust Chapter 1 predicates
`Homogenization.Book.Ch01.PotentialZeroTraceFieldOn` and
`Homogenization.Book.Ch01.SolenoidalZeroNormalTraceFieldOn`, which are the ones
appearing in `Homogenization.Book.Ch02.IsDoubledMuAdmissible`.
-/

namespace Algsuperdiff
namespace Section3
namespace Provider
namespace Whitney

open HCPolySupport
open MeasureTheory

variable {d : ℕ}

/-! ## `L²` bookkeeping for functions supported in a subset -/

/-- A function vanishing off `V ⊆ U` has the same `L²` norm over `U` and over `V`. -/
theorem eLpNorm_two_restrict_eq_of_zero_outside {U V : Set (Vec d)} (hV : MeasurableSet V)
    (hVU : V ⊆ U) {h : Vec d → ℝ} (hzero : ∀ x, x ∉ V → h x = 0) :
    eLpNorm h 2 (volume.restrict U) = eLpNorm h 2 (volume.restrict V) := by
  have hind : V.indicator h = h := by
    funext x
    by_cases hx : x ∈ V
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx, hzero x hx]
  calc
    eLpNorm h 2 (volume.restrict U)
        = eLpNorm (V.indicator h) 2 (volume.restrict U) := by rw [hind]
    _ = eLpNorm h 2 ((volume.restrict U).restrict V) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hV
    _ = eLpNorm h 2 (volume.restrict V) := by
        rw [Measure.restrict_restrict hV, Set.inter_eq_self_of_subset_left hVU]

/-- Extension by zero preserves scalar `L²` membership across an inclusion. -/
theorem memL2On_indicator_of_subset {U V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ U)
    {h : Vec d → ℝ} (hh : MemL2On V h) : MemL2On U (V.indicator h) := by
  refine (memLp_indicator_iff_restrict hV).2 ?_
  rwa [Measure.restrict_restrict hV, Set.inter_eq_self_of_subset_left hVU]

/-- Extension by zero preserves vector `L²` membership across an inclusion. -/
theorem memVectorL2_indicator_of_subset {U V : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ U)
    {f : Vec d → Vec d} (hf : MemVectorL2 V f) : MemVectorL2 U (V.indicator f) := by
  refine (memLp_indicator_iff_restrict hV).2 ?_
  rwa [Measure.restrict_restrict hV, Set.inter_eq_self_of_subset_left hVU]

/-- Coordinates of a vector indicator are indicators of the coordinates. -/
theorem indicator_apply_coord (V : Set (Vec d)) (f : Vec d → Vec d) (i : Fin d) (x : Vec d) :
    (V.indicator f x) i = V.indicator (fun y => f y i) x := by
  by_cases hx : x ∈ V
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

/-! ## Extension by zero of `H¹₀` -/

/-- **Extension by zero of an `H¹₀` function across an inclusion.**  For `V ⊆ U`
with `V` measurable and `U` open, the function `1_V u`, with gradient `1_V ∇u`,
belongs to `H¹₀(U)`. -/
noncomputable def extendZeroH10 {U V : Set (Vec d)} (hU : IsOpen U) (hV : MeasurableSet V)
    (hVU : V ⊆ U) (u : H10Function V) : H10Function U := by
  classical
  have hzeroFun : ∀ n : ℕ, ∀ x : Vec d, x ∉ V → u.approx n x = 0 := by
    intro n x hx
    exact image_eq_zero_of_notMem_tsupport fun hmem => hx (u.approx_support_subset n hmem)
  have hzeroDeriv : ∀ n : ℕ, ∀ x : Vec d, x ∉ V → fderiv ℝ (u.approx n) x = 0 := by
    intro n x hx
    have hx_notin : x ∉ tsupport (u.approx n) := fun hmem => hx (u.approx_support_subset n hmem)
    have heq : u.approx n =ᶠ[nhds x] 0 :=
      ((isClosed_tsupport (f := u.approx n)).isOpen_compl.eventually_mem hx_notin).mono
        fun y hy => image_eq_zero_of_notMem_tsupport hy
    rw [Filter.EventuallyEq.fderiv_eq heq]
    simp
  -- the approximants, viewed as `H¹(U)` functions
  let A : ℕ → H1Function U := fun n =>
    H1Function.ofContDiff hU ((u.approx_smooth n).of_le (by simp))
      (u.approx_hasCompactSupport n)
  have hAtoFun : ∀ n : ℕ, (A n).toFun = u.approx n := fun _ => rfl
  have hAgrad : ∀ (n : ℕ) (x : Vec d) (i : Fin d),
      (A n).grad x i = (fderiv ℝ (u.approx n) x) (basisVec i) := fun _ _ _ => rfl
  -- the extended data
  have hMemL2 : MemL2On U (V.indicator u.toH1Function.toFun) :=
    memL2On_indicator_of_subset hV hVU u.toH1Function.memL2
  have hGradMemL2 : GradMemL2On U (V.indicator u.toH1Function.grad) := by
    intro i
    have h := memL2On_indicator_of_subset hV hVU (u.toH1Function.gradMemL2 i)
    have hfun :
        (fun x => (V.indicator u.toH1Function.grad x) i) =
          V.indicator fun y => u.toH1Function.grad y i := by
      funext x
      exact indicator_apply_coord V u.toH1Function.grad i x
    rw [hfun]
    exact h
  have htendFun :
      Filter.Tendsto
        (fun n => eLpNorm (fun x => u.approx n x - V.indicator u.toH1Function.toFun x) 2
          (volume.restrict U))
        Filter.atTop (nhds 0) := by
    have hcongr : ∀ n : ℕ,
        eLpNorm (fun x => u.approx n x - V.indicator u.toH1Function.toFun x) 2
            (volume.restrict U) =
          eLpNorm (fun x => u.approx n x - u.toH1Function.toFun x) 2 (volume.restrict V) := by
      intro n
      have hzero : ∀ x : Vec d, x ∉ V →
          u.approx n x - V.indicator u.toH1Function.toFun x = 0 := by
        intro x hx
        simp [hzeroFun n x hx, Set.indicator_of_notMem hx]
      rw [eLpNorm_two_restrict_eq_of_zero_outside hV hVU hzero]
      refine eLpNorm_congr_ae ?_
      refine (ae_restrict_iff' hV).2 (Filter.Eventually.of_forall ?_)
      intro x hx
      simp [Set.indicator_of_mem hx]
    simpa [hcongr] using u.tendsto_approx
  have htendGrad : ∀ i : Fin d,
      Filter.Tendsto
        (fun n => eLpNorm
          (fun x => (A n).grad x i - (V.indicator u.toH1Function.grad x) i) 2
          (volume.restrict U))
        Filter.atTop (nhds 0) := by
    intro i
    have hcongr : ∀ n : ℕ,
        eLpNorm (fun x => (A n).grad x i - (V.indicator u.toH1Function.grad x) i) 2
            (volume.restrict U) =
          eLpNorm (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i) 2
            (volume.restrict V) := by
      intro n
      have hzero : ∀ x : Vec d, x ∉ V →
          (A n).grad x i - (V.indicator u.toH1Function.grad x) i = 0 := by
        intro x hx
        simp [hAgrad n x i, hzeroDeriv n x hx, Set.indicator_of_notMem hx]
      rw [eLpNorm_two_restrict_eq_of_zero_outside hV hVU hzero]
      refine eLpNorm_congr_ae ?_
      refine (ae_restrict_iff' hV).2 (Filter.Eventually.of_forall ?_)
      intro x hx
      simp [hAgrad n x i, Set.indicator_of_mem hx]
    simpa [hcongr] using u.tendsto_approx_grad i
  refine
    { toH1Function :=
        { toFun := V.indicator u.toH1Function.toFun
          grad := V.indicator u.toH1Function.grad
          memL2 := hMemL2
          gradMemL2 := hGradMemL2
          hasWeakGradient := ?_ }
      approx := u.approx
      approx_smooth := u.approx_smooth
      approx_hasCompactSupport := u.approx_hasCompactSupport
      approx_support_subset := fun n => (u.approx_support_subset n).trans hVU
      tendsto_approx := htendFun
      tendsto_approx_grad := htendGrad }
  exact HasWeakGradientOn.of_tendsto_eLpNorm_two hMemL2 hGradMemL2
    (fun n => (A n).memL2) (fun n => (A n).gradMemL2)
    (fun n => (A n).hasWeakGradient) (by simpa [hAtoFun] using htendFun) htendGrad

@[simp] theorem extendZeroH10_grad {U V : Set (Vec d)} (hU : IsOpen U) (hV : MeasurableSet V)
    (hVU : V ⊆ U) (u : H10Function V) :
    (extendZeroH10 hU hV hVU u).toH1Function.grad = V.indicator u.toH1Function.grad :=
  rfl

/-! ## Extension by zero of the Chapter 1 field spaces -/

/-- Extension by zero maps `L²_{pot,0}(V)` into `L²_{pot,0}(U)` for `V ⊆ U`. -/
theorem potentialZeroTraceFieldOn_indicator_of_subset {U V : Set (Vec d)} (hU : IsOpen U)
    (hV : MeasurableSet V) (hVU : V ⊆ U) {f : Vec d → Vec d}
    (hf : Book.Ch01.PotentialZeroTraceFieldOn V f) :
    Book.Ch01.PotentialZeroTraceFieldOn U (V.indicator f) := by
  obtain ⟨hmem, u, hae⟩ := hf
  refine ⟨memVectorL2_indicator_of_subset hV hVU hmem, extendZeroH10 hU hV hVU u, ?_⟩
  rw [extendZeroH10_grad]
  have hae' : ∀ᵐ x ∂volume, x ∈ V → f x = u.toH1Function.grad x :=
    (ae_restrict_iff' hV).1 hae
  refine (ae_restrict_iff' hU.measurableSet).2 ?_
  filter_upwards [hae'] with x hx _
  by_cases hxV : x ∈ V
  · simp [Set.indicator_of_mem hxV, hx hxV]
  · simp [Set.indicator_of_notMem hxV]

/-- Extension by zero maps `L²_{sol,0}(V)` into `L²_{sol,0}(U)` for `V ⊆ U`. -/
theorem solenoidalZeroNormalTraceFieldOn_indicator_of_subset {U V : Set (Vec d)}
    (hVopen : IsOpen V) (hVU : V ⊆ U) {g : Vec d → Vec d}
    (hg : Book.Ch01.SolenoidalZeroNormalTraceFieldOn V g) :
    Book.Ch01.SolenoidalZeroNormalTraceFieldOn U (V.indicator g) := by
  obtain ⟨hmem, horth⟩ := hg
  refine ⟨memVectorL2_indicator_of_subset hVopen.measurableSet hVU hmem, ?_⟩
  intro φ
  have hfun : (fun x => vecDot (V.indicator g x) (φ.grad x)) =
      V.indicator fun y => vecDot (g y) (φ.grad y) := by
    funext x
    by_cases hx : x ∈ V
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx, vecDot]
  calc
    ∫ x in U, vecDot (V.indicator g x) (φ.grad x) ∂volume
        = ∫ x in U, V.indicator (fun y => vecDot (g y) (φ.grad y)) x ∂volume := by
          rw [hfun]
    _ = ∫ x in U ∩ V, vecDot (g x) (φ.grad x) ∂volume :=
          setIntegral_indicator hVopen.measurableSet
    _ = ∫ x in V, vecDot (g x) (φ.grad x) ∂volume := by
          rw [Set.inter_eq_self_of_subset_right hVU]
    _ = 0 := horth (φ.restrict hVopen hVU)

/-! ## Closure of the Chapter 1 field spaces under sums -/

theorem potentialZeroTraceFieldOn_add {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hf : Book.Ch01.PotentialZeroTraceFieldOn U f)
    (hg : Book.Ch01.PotentialZeroTraceFieldOn U g) :
    Book.Ch01.PotentialZeroTraceFieldOn U (fun x => f x + g x) := by
  obtain ⟨hfmem, u, hfae⟩ := hf
  obtain ⟨hgmem, v, hgae⟩ := hg
  refine ⟨hfmem.add hgmem, u + v, ?_⟩
  filter_upwards [hfae, hgae] with x hx hy
  change f x + g x = (u.toH1Function + v.toH1Function).grad x
  rw [H1Function.add_grad]
  simp [hx, hy]

theorem solenoidalZeroNormalTraceFieldOn_add {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hf : Book.Ch01.SolenoidalZeroNormalTraceFieldOn U f)
    (hg : Book.Ch01.SolenoidalZeroNormalTraceFieldOn U g) :
    Book.Ch01.SolenoidalZeroNormalTraceFieldOn U (fun x => f x + g x) :=
  ⟨hf.1.add hg.1, isSolenoidalZeroNormalTraceOn_add_of_memVectorL2 hf.1 hg.1 hf.2 hg.2⟩

theorem potentialZeroTraceFieldOn_zero {U : Set (Vec d)} :
    Book.Ch01.PotentialZeroTraceFieldOn U (fun _ : Vec d => (0 : Vec d)) :=
  ⟨MeasureTheory.MemLp.zero, 0, by rfl⟩

theorem solenoidalZeroNormalTraceFieldOn_zero {U : Set (Vec d)} :
    Book.Ch01.SolenoidalZeroNormalTraceFieldOn U (fun _ : Vec d => (0 : Vec d)) :=
  ⟨MeasureTheory.MemLp.zero, isSolenoidalZeroNormalTraceOn_zero⟩

theorem potentialZeroTraceFieldOn_sum {ι : Type} (s : Finset ι) {U : Set (Vec d)}
    (F : ι → Vec d → Vec d)
    (h : ∀ i ∈ s, Book.Ch01.PotentialZeroTraceFieldOn U (F i)) :
    Book.Ch01.PotentialZeroTraceFieldOn U (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (potentialZeroTraceFieldOn_zero (U := U))
  | insert i s hi ih =>
      have hmem := h i (Finset.mem_insert_self i s)
      have hrest := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
      have := potentialZeroTraceFieldOn_add hmem hrest
      simpa [Finset.sum_insert hi] using this

theorem solenoidalZeroNormalTraceFieldOn_sum {ι : Type} (s : Finset ι) {U : Set (Vec d)}
    (F : ι → Vec d → Vec d)
    (h : ∀ i ∈ s, Book.Ch01.SolenoidalZeroNormalTraceFieldOn U (F i)) :
    Book.Ch01.SolenoidalZeroNormalTraceFieldOn U (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (solenoidalZeroNormalTraceFieldOn_zero (U := U))
  | insert i s hi ih =>
      have hmem := h i (Finset.mem_insert_self i s)
      have hrest := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
      have := solenoidalZeroNormalTraceFieldOn_add hmem hrest
      simpa [Finset.sum_insert hi] using this

end Whitney
end Provider
end Section3
end Algsuperdiff
