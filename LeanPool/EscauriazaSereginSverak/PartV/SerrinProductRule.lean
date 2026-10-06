/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Products of primitives of integrable functions

If two functions are primitives of integrable functions on `[0, T]`, their
product is the primitive of the product-rule expression. This is the
one-dimensional calculus used to differentiate the mollified cross pairing in
`lem:pv-serrin-uniqueness`.
-/

public section

open MeasureTheory Set Filter
open scoped Topology


noncomputable section

namespace ESS

private theorem serrin_primitive_ac {T c : ℝ} {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioo 0 T)) (t : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun x => c + ∫ τ in (0 : ℝ)..x, (Ioo 0 T).indicator f τ) 0 t := by
  have hint : Integrable ((Ioo 0 T).indicator f) volume :=
    hf.integrable_indicator measurableSet_Ioo
  have hinterval := hint.intervalIntegrable (a := 0) (b := t)
  have hac := hinterval.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) 0 t :=
    (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval
  exact hconst.add hac

private theorem serrin_primitive_deriv_ae {T c t : ℝ} {f : ℝ → ℝ}
    (hf : IntegrableOn f (Ioo 0 T)) :
    ∀ᵐ x, x ∈ uIcc 0 t →
      deriv (fun x => c + ∫ τ in (0 : ℝ)..x, (Ioo 0 T).indicator f τ) x =
        (Ioo 0 T).indicator f x := by
  have hint : Integrable ((Ioo 0 T).indicator f) volume :=
    hf.integrable_indicator measurableSet_Ioo
  filter_upwards [(hint.intervalIntegrable (a := 0) (b := t)).ae_hasDerivAt_integral]
    with x hx hxI
  exact ((hx hxI 0 (by simp)).const_add c).deriv

/-- The product of two primitives of integrable functions on `(0, T)` is the
primitive of `f G + F g`, from the value at time zero. -/
theorem serrin_primitive_product {T : ℝ} {F G f g : ℝ → ℝ}
    (hf : IntegrableOn f (Ioo 0 T)) (hg : IntegrableOn g (Ioo 0 T))
    (hF : ∀ t ∈ Icc 0 T, F t = F 0 + ∫ τ in (0 : ℝ)..t, f τ)
    (hG : ∀ t ∈ Icc 0 T, G t = G 0 + ∫ τ in (0 : ℝ)..t, g τ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    F t * G t = F 0 * G 0 + ∫ τ in (0 : ℝ)..t, (f τ * G τ + F τ * g τ) := by
  let fI : ℝ → ℝ := (Ioo 0 T).indicator f
  let gI : ℝ → ℝ := (Ioo 0 T).indicator g
  let Ft : ℝ → ℝ := fun x => F 0 + ∫ τ in (0 : ℝ)..x, fI τ
  let Gt : ℝ → ℝ := fun x => G 0 + ∫ τ in (0 : ℝ)..x, gI τ
  have hFac : AbsolutelyContinuousOnInterval Ft 0 t := serrin_primitive_ac hf t
  have hGac : AbsolutelyContinuousOnInterval Gt 0 t := serrin_primitive_ac hg t
  have hmain := hFac.integral_deriv_mul_eq_sub hGac
  -- identify the primitives with the given functions on the closed interval
  have hIcc (x : ℝ) (hx : x ∈ uIcc 0 t) : x ∈ Icc 0 T := by
    rw [uIcc_of_le ht.1] at hx
    exact ⟨hx.1, hx.2.trans ht.2⟩
  have hprim_eq {h H : ℝ → ℝ}
      (hH : ∀ s ∈ Icc 0 T, H s = H 0 + ∫ τ in (0 : ℝ)..s, h τ)
      (x : ℝ) (hx : x ∈ Icc 0 T) :
      H 0 + ∫ τ in (0 : ℝ)..x, (Ioo 0 T).indicator h τ = H x := by
    rw [hH x hx]
    congr 1
    apply intervalIntegral.integral_congr_ae
    filter_upwards [Measure.ae_ne volume T] with r hrT hr
    rw [uIoc_of_le hx.1] at hr
    have hrI : r ∈ Ioo 0 T := ⟨hr.1, lt_of_le_of_ne (hr.2.trans hx.2) hrT⟩
    simp [hrI]
  have hFt (x : ℝ) (hx : x ∈ uIcc 0 t) : Ft x = F x := hprim_eq hF x (hIcc x hx)
  have hGt (x : ℝ) (hx : x ∈ uIcc 0 t) : Gt x = G x := hprim_eq hG x (hIcc x hx)
  have h0 : (0 : ℝ) ∈ uIcc 0 t := by simp
  have htt : t ∈ uIcc 0 t := by simp
  rw [hFt t htt, hGt t htt, hFt 0 h0, hGt 0 h0] at hmain
  have hcongr : (∫ τ in (0 : ℝ)..t, deriv Ft τ * Gt τ + Ft τ * deriv Gt τ) =
      ∫ τ in (0 : ℝ)..t, (f τ * G τ + F τ * g τ) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [serrin_primitive_deriv_ae (c := F 0) (t := t) hf,
      serrin_primitive_deriv_ae (c := G 0) (t := t) hg, Measure.ae_ne volume T]
      with r hdF hdG hrT hr
    have hrIcc : r ∈ uIcc 0 t := uIoc_subset_uIcc hr
    rw [uIoc_of_le ht.1] at hr
    have hrI : r ∈ Ioo 0 T := ⟨hr.1, lt_of_le_of_ne (hr.2.trans ht.2) hrT⟩
    change deriv Ft r * Gt r + Ft r * deriv Gt r = _
    rw [hdF hrIcc, hdG hrIcc, hFt r hrIcc, hGt r hrIcc]
    simp [hrI]
  rw [hcongr] at hmain
  linarith only [hmain]

end ESS
