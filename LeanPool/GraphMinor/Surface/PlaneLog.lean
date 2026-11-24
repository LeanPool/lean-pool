/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Continuous logarithms

The topology of the plane in this development rests on one tool: continuous logarithms of
functions with no zeros. This file sets them up.

`HasLogOn X f` says that `f` has a continuous logarithm on the set `X`. The main facts are:
- a homotopy of nonvanishing functions starting at the constant `1` has a continuous logarithm
  (`exists_log_of_homotopy`), by the homotopy lifting property of the covering `exp`;
- so nonvanishing functions on the plane, and on the unit interval, have logarithms
  (`hasLogOn_univ_of_ne_zero`, `hasLogOn_unitInterval`);
- the function $(z - a)^m$ has no logarithm on a circle around $a$ unless $m = 0$
  (`eq_zero_of_hasLogOn_sphere`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Complex

local notation "𝕀" => unitInterval

universe u

/-- The function `f` has a continuous logarithm on the set `X`. -/
def HasLogOn {T : Type u} [TopologicalSpace T] (X : Set T) (f : T → ℂ) : Prop :=
  ∃ g : T → ℂ, ContinuousOn g X ∧ ∀ x ∈ X, f x = exp (g x)

section Basic

variable {T : Type u} [TopologicalSpace T] {X Y : Set T} {f f₁ f₂ : T → ℂ}

theorem HasLogOn.mono (h : HasLogOn Y f) (hX : X ⊆ Y) : HasLogOn X f := by
  obtain ⟨g, hg, hf⟩ := h
  exact ⟨g, hg.mono hX, fun x hx => hf x (hX hx)⟩

theorem HasLogOn.congr (h : HasLogOn X f₁) (hf : ∀ x ∈ X, f₂ x = f₁ x) : HasLogOn X f₂ := by
  obtain ⟨g, hg, hf'⟩ := h
  exact ⟨g, hg, fun x hx => (hf x hx).trans (hf' x hx)⟩

theorem HasLogOn.mul (h₁ : HasLogOn X f₁) (h₂ : HasLogOn X f₂) :
    HasLogOn X fun x => f₁ x * f₂ x := by
  obtain ⟨g₁, hg₁, hf₁⟩ := h₁
  obtain ⟨g₂, hg₂, hf₂⟩ := h₂
  exact ⟨fun x => g₁ x + g₂ x, hg₁.add hg₂, fun x hx => by
    simp only [hf₁ x hx, hf₂ x hx, exp_add]⟩

theorem HasLogOn.inv (h : HasLogOn X f) : HasLogOn X fun x => (f x)⁻¹ := by
  obtain ⟨g, hg, hf⟩ := h
  exact ⟨fun x => - g x, hg.neg, fun x hx => by
    simp only [hf x hx, exp_neg]⟩

theorem HasLogOn.div (h₁ : HasLogOn X f₁) (h₂ : HasLogOn X f₂) :
    HasLogOn X fun x => f₁ x / f₂ x := by
  simpa [div_eq_mul_inv] using h₁.mul h₂.inv

theorem HasLogOn.zpow (h : HasLogOn X f) (m : ℤ) : HasLogOn X fun x => f x ^ m := by
  obtain ⟨g, hg, hf⟩ := h
  refine ⟨fun x => (m : ℂ) * g x, continuousOn_const.mul hg, fun x hx => ?_⟩
  simp only [hf x hx, exp_int_mul]

theorem hasLogOn_const {c : ℂ} (hc : c ≠ 0) : HasLogOn X fun _ => c :=
  ⟨fun _ => log c, continuousOn_const, fun _ _ => (exp_log hc).symm⟩

/-- A function with values in the slit plane has a logarithm: the principal one. -/
theorem hasLogOn_of_slitPlane (hf : ContinuousOn f X) (h : ∀ x ∈ X, f x ∈ slitPlane) :
    HasLogOn X f :=
  ⟨fun x => log (f x), hf.clog h, fun x hx => (exp_log (slitPlane_ne_zero (h x hx))).symm⟩

/-- A continuous function on a preconnected set with values in $2 \pi i \mathbb{Z}$ is constant. -/
theorem eq_of_exp_eq_one {g : T → ℂ} (hX : IsPreconnected X) (hg : ContinuousOn g X)
    (h : ∀ x ∈ X, exp (g x) = 1) {x y : T} (hx : x ∈ X) (hy : y ∈ X) : g x = g y := by
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hint : ∀ x ∈ X, ∃ n : ℤ, g x = n * (2 * Real.pi * I) := fun x hx =>
    Complex.exp_eq_one_iff.mp (h x hx)
  have hre : ContinuousOn (fun x => (g x / (2 * Real.pi * I)).re) X :=
    Complex.continuous_re.comp_continuousOn (hg.div_const _)
  have himg : (fun x => (g x / (2 * Real.pi * I)).re) '' X ⊆ range ((↑) : ℤ → ℝ) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨n, hn⟩ := hint x hx
    refine ⟨n, ?_⟩
    change _ = (g x / (2 * Real.pi * I)).re
    rw [hn, mul_div_assoc, div_self hpi, mul_one]
    simp
  have htd : IsTotallyDisconnected (range ((↑) : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isEmbedding.isTotallyDisconnected_range.mpr inferInstance
  have hsub := htd _ himg (hX.image _ hre)
  have heq := hsub (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)
  obtain ⟨n, hn⟩ := hint x hx
  obtain ⟨k, hk⟩ := hint y hy
  have hdiv : ∀ n : ℤ, ((n : ℂ) * (2 * Real.pi * I) / (2 * Real.pi * I)).re = n := fun n => by
    rw [mul_div_assoc, div_self hpi, mul_one]
    simp
  have heq' : (g x / (2 * Real.pi * I)).re = (g y / (2 * Real.pi * I)).re := heq
  rw [hn, hk, hdiv, hdiv, Int.cast_inj] at heq'
  have heq := heq'
  rw [hn, hk, heq]

theorem hasLogOn_iff_subtype {K : Set T} {f : T → ℂ} :
    HasLogOn K f ↔ ∃ g : C(K, ℂ), ∀ x : K, f x = exp (g x) := by
  classical
  constructor
  · rintro ⟨g, hg, hf⟩
    exact ⟨⟨K.domRestrict g, continuousOn_iff_continuous_domRestrict.mp hg⟩, fun x => hf x x.2⟩
  · rintro ⟨g, hf⟩
    refine ⟨fun x => if h : x ∈ K then g ⟨x, h⟩ else 0, ?_, fun x hx => ?_⟩
    · rw [continuousOn_iff_continuous_domRestrict]
      convert g.continuous using 1
      ext x
      simp [Set.domRestrict, x.2]
    · simp only [hx, dite_true]
      exact hf ⟨x, hx⟩

end Basic

section Homotopy

/-- A homotopy of nonvanishing functions that starts at the constant `1` has a continuous
logarithm that starts at `0`. Route: the homotopy lifting property of the covering
`Complex.isCoveringMap_exp`. -/
theorem exists_log_of_homotopy {A : Type u} [TopologicalSpace A] (H : C(𝕀 × A, ℂ))
    (h0 : ∀ a, H (0, a) = 1) (hne : ∀ p, H p ≠ 0) :
    ∃ g : C(𝕀 × A, ℂ), (∀ p, exp (g p) = H p) ∧ ∀ a, g (0, a) = 0 := by
  let H' : C(𝕀 × A, {z : ℂ // z ≠ 0}) := ⟨fun p => ⟨H p, hne p⟩, by fun_prop⟩
  have hH0 : ∀ a, H' (0, a) = (fun z : ℂ => (⟨exp z, exp_ne_zero z⟩ : {z : ℂ // z ≠ 0}))
      ((ContinuousMap.const A (0 : ℂ)) a) := by
    intro a
    apply Subtype.ext
    simp [H', h0]
  let G := isCoveringMap_exp.liftHomotopy H' (ContinuousMap.const A (0 : ℂ)) hH0
  refine ⟨G, fun p => ?_, fun a => ?_⟩
  · have := congr_fun (isCoveringMap_exp.liftHomotopy_lifts H' (ContinuousMap.const A
    (0 : ℂ)) hH0) p
    exact congr_arg Subtype.val this
  · exact isCoveringMap_exp.liftHomotopy_zero H' (ContinuousMap.const A (0 : ℂ)) hH0 a

variable {T : Type u} [TopologicalSpace T]

/-- If `H` is a homotopy of nonvanishing functions on `K` from the constant `1` to `f`, then `f`
has a logarithm on `K`. -/
theorem hasLogOn_of_homotopy {K : Set T} (H : 𝕀 → T → ℂ)
    (hc : ContinuousOn (fun p : 𝕀 × T => H p.1 p.2) (univ ×ˢ K))
    (h0 : ∀ x ∈ K, H 0 x = 1) (hne : ∀ t, ∀ x ∈ K, H t x ≠ 0) :
    HasLogOn K (H 1) := by
  rw [hasLogOn_iff_subtype]
  let H' : C(𝕀 × K, ℂ) := ⟨fun p => H p.1 p.2.1, by
    have : Continuous (fun p : 𝕀 × K => ((p.1, p.2.1) : 𝕀 × T)) := by fun_prop
    exact hc.comp_continuous this fun p => ⟨mem_univ _, p.2.2⟩⟩
  obtain ⟨g, hg, -⟩ := exists_log_of_homotopy H' (fun a => h0 a a.2)
    (fun p => hne p.1 p.2 p.2.2)
  exact ⟨⟨fun x => g (1, x), by fun_prop⟩, fun x => (hg (1, x)).symm⟩

/-- A nonvanishing continuous function on a real vector space has a logarithm: contract the space
to the origin. -/
theorem hasLogOn_univ_of_ne_zero {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} (hf : Continuous f) (hne : ∀ x, f x ≠ 0) : HasLogOn univ f := by
  have h := hasLogOn_of_homotopy (K := (univ : Set E))
    (fun t x => f ((t : ℝ) • x) / f 0)
    (by apply Continuous.continuousOn; fun_prop)
    (fun x _ => by simp [hne 0]) (fun t x _ => div_ne_zero (hne _) (hne 0))
  have h2 := h.mul (hasLogOn_const (hne 0))
  refine h2.congr fun x _ => ?_
  simp [hne 0]

/-- Every nonvanishing continuous function on the unit interval has a logarithm. -/
theorem hasLogOn_unitInterval {f : 𝕀 → ℂ} (hf : Continuous f) (hne : ∀ t, f t ≠ 0) :
    HasLogOn (univ : Set 𝕀) f := by
  have h := hasLogOn_of_homotopy (K := (univ : Set 𝕀))
    (fun t x => f (⟨(t : ℝ) * x, unitInterval.mul_mem t.2 x.2⟩ : 𝕀) / f 0)
    (by apply Continuous.continuousOn; fun_prop)
    (fun x _ => by simp [hne 0]) (fun t x _ => div_ne_zero (hne _) (hne 0))
  have h2 := h.mul (hasLogOn_const (hne 0))
  refine h2.congr fun x _ => ?_
  simp [hne 0]

/-- A nonvanishing continuous function has a logarithm on any homeomorphic image of the unit
interval. -/
theorem hasLogOn_of_arc {L : Set T} (φ : 𝕀 ≃ₜ L) {f : T → ℂ} (hf : ContinuousOn f L)
    (hne : ∀ x ∈ L, f x ≠ 0) : HasLogOn L f := by
  have hcont : Continuous fun t : 𝕀 => f (φ t).1 :=
    hf.comp_continuous (by fun_prop) fun t => (φ t).2
  obtain ⟨g, hg, hfg⟩ := hasLogOn_unitInterval hcont fun t => hne _ (φ t).2
  rw [hasLogOn_iff_subtype]
  refine ⟨⟨fun x => g (φ.symm x), ?_⟩, fun x => ?_⟩
  · exact (continuousOn_univ.mp hg).comp φ.symm.continuous
  · have := hfg (φ.symm x) (mem_univ _)
    simpa using this

/-- A logarithm of `f ∘ g` on a compact set `K`, with `g` injective on `K`, gives a logarithm of `f`
on the image of `K`. -/
theorem hasLogOn_image {T' : Type*} [TopologicalSpace T'] [T2Space T'] {K : Set T}
  (hK : IsCompact K)
    {g : T → T'} (hg : ContinuousOn g K) (hinj : InjOn g K) {f : T' → ℂ}
    (h : HasLogOn K fun x => f (g x)) : HasLogOn (g '' K) f := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let e₀ : K ≃ g '' K := Equiv.Set.imageOfInjOn g K hinj
  have he₀ : Continuous e₀ :=
    (continuousOn_iff_continuous_domRestrict.mp hg).subtype_mk _
  let e : K ≃ₜ g '' K := he₀.homeoOfEquivCompactToT2
  obtain ⟨l, hl⟩ := hasLogOn_iff_subtype.mp h
  rw [hasLogOn_iff_subtype]
  refine ⟨⟨fun y => l (e.symm y), by fun_prop⟩, fun y => ?_⟩
  have h1 := hl (e.symm y)
  have h2 : g (e.symm y).1 = y.1 := congr_arg Subtype.val (e.apply_symm_apply y)
  rw [← h2]
  exact h1

end Homotopy

section Circle

/-- The function $(z - a)^m$ has no logarithm on a circle around `a`, unless `m = 0`. Going once
around the circle would change the logarithm by $2 \pi i m$. -/
theorem eq_zero_of_hasLogOn_sphere {a : ℂ} {R : ℝ} (hR : 0 < R) {m : ℤ}
    (h : HasLogOn (Metric.sphere a R) fun z => (z - a) ^ m) : m = 0 := by
  obtain ⟨g, hg, hf⟩ := h
  let c : ℝ → ℂ := fun t => a + R * exp (t * I)
  have hc : Continuous c := by fun_prop
  have hmem : ∀ t, c t ∈ Metric.sphere a R := fun t => by
    simp only [Metric.mem_sphere, dist_eq_norm, c, add_sub_cancel_left, norm_mul, norm_real,
      norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs, abs_of_pos hR]
  let k : ℝ → ℂ := fun t => g (c t) - m * (t * I) - m * log R
  have hk : Continuous k := by
    have : Continuous fun t => g (c t) := hg.comp_continuous hc hmem
    exact (this.sub (continuous_const.mul (continuous_ofReal.mul continuous_const))).sub
      continuous_const
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hexp : ∀ t ∈ (univ : Set ℝ), exp (k t) = 1 := by
    intro t _
    have h1 : (c t - a) ^ m = _ := hf (c t) (hmem t)
    have h2 : c t - a = R * exp (t * I) := by simp [c]
    rw [h2, mul_zpow] at h1
    have h3 : exp (m * (t * I)) = exp (t * I) ^ m := exp_int_mul _ _
    have h4 : exp (m * log R) = (R : ℂ) ^ m := by rw [exp_int_mul, exp_log hR']
    simp only [k]
    rw [exp_sub, exp_sub, ← h1, h3, h4]
    have h5 : exp (t * I) ≠ 0 := exp_ne_zero _
    have h6 : (R : ℂ) ^ m ≠ 0 := zpow_ne_zero _ hR'
    have h7 : exp (t * I) ^ m ≠ 0 := zpow_ne_zero _ h5
    field_simp
  have heq := eq_of_exp_eq_one isPreconnected_univ hk.continuousOn hexp
    (mem_univ (2 * Real.pi)) (mem_univ 0)
  have hc2 : c (2 * Real.pi) = c 0 := by
    simp only [c]
    push_cast
    rw [exp_two_pi_mul_I]
    simp
  simp only [k, hc2] at heq
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have : (m : ℂ) * (2 * Real.pi * I) = 0 := by
    push_cast at heq
    linear_combination -heq
  have hm : (m : ℂ) = 0 := (mul_eq_zero.mp this).resolve_right hpi
  exact_mod_cast hm

end Circle

end GraphMinor.Surface
