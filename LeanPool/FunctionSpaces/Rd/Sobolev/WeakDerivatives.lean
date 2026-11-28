/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Fourier.SchwartzCutoff

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Weak derivatives and Sobolev spaces on open sets

Let `V` be a finite-dimensional real inner product space, such as `ℝ^d`, with Lebesgue measure,
and `Ω ⊆ V` open. For directions `v = (v_0, …, v_{k-1})` in `V`,
`∂^v = ∂_{v_0} ⋯ ∂_{v_{k-1}}` is the iterated directional derivative (Mathlib's
`LineDeriv.iteratedLineDerivOp`, notation `∂^{v}`). A locally integrable function `f` on `Ω` is
the distribution `φ ↦ ∫ φ f` on `Ω` (Mathlib's `Distribution.ofFun`, test functions
`𝓓(Ω, ℝ)`), and Mathlib differentiates distributions by `∂_w T (φ) = T(-∂_w φ)`.

* **Weak derivatives** (`Rd.HasWeakLineDeriv Ω v f g`): `∂^v f = g` as distributions on `Ω`,
  that is, `∫ φ g = (-1)^k ∫ (∂^v φ) f` for every test function `φ`
  (`Rd.hasWeakLineDeriv_iff_integral`, by the transpose formula
  `Distribution.iteratedLineDerivOp_apply_apply`). They are unique almost everywhere on `Ω`
  and, on `V`, unique as elements of `L_r(V)` (`Rd.HasWeakLineDeriv.eq_of_top`), linear, local
  (`Rd.HasWeakLineDeriv.mono`), on `V` locally integrable, as is `f`
  (`Rd.HasWeakLineDeriv.locallyIntegrable_deriv`, `Rd.HasWeakLineDeriv.locallyIntegrable`),
  iterate (`Rd.HasWeakLineDeriv.of_cons`: if `G = ∂^v f` and `H = ∂^{(w, v)} f`, then
  `H = ∂_w G`), vanish where `f` vanishes
  (`Rd.HasWeakLineDeriv.ae_eq_zero_of_ae_eq_zero`), additive over finite sums
  (`Rd.HasWeakLineDeriv.sum`), tested also by smooth compactly supported complex functions
  (`Rd.HasWeakLineDeriv.integral_mul_eq`), satisfy the product rule with smooth real functions
  `χ` (`Rd.HasWeakLineDeriv.mul_contDiff`), also from `Ω ∩ B` to `Ω` when the closed support of
  `χ` lies in an open set `B` (`Rd.HasWeakLineDeriv.mul_of_tsupport_subset`, through the test
  functions `Rd.testFunctionMulOn`), are classical on Schwartz functions
  (`Rd.hasWeakLineDeriv_schwartz`), and pass to limits in `L_p(Ω)`
  (`Rd.HasWeakLineDeriv.of_tendsto`).
* **Sobolev spaces**: `Rd.MemWeakSobolev Ω m p f` says that `f` and all its weak derivatives of
  order at most `m` lie in `L_p(Ω)`; `Rd.MemSobolev m f` is the case `Ω = V` for `f ∈ L_p(V)`,
  with the weak derivatives as classes in `L_p(V)` (`Rd.memSobolev_iff_exists_hasWeakLineDeriv`;
  for `m = 1`, weak derivatives in every direction suffice,
  `Rd.memSobolev_one_of_forall_hasWeakLineDeriv`), closed under finite sums
  (`Rd.MemSobolev.sum`).
* **The bridge to tempered distributions** (`Rd.hasWeakLineDeriv_top_iff`): for `f ∈ L_p(V)`,
  `g ∈ L_r(V)`, the weak derivative on `V` is the derivative of tempered distributions,
  `∂^v f = g` in `𝓢'(V, ℂ)`, since a tempered distribution that vanishes on all test functions
  is zero (`Rd.eq_zero_of_testSchwartz`).
-/

@[expose] public section

open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal SchwartzMap LineDeriv Distributions

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### Weak derivatives on open sets -/

/-- `g` is the **weak derivative** `∂^v f` of `f` on the open set `Ω` along the directions
`v = (v_0, …, v_{k-1})`: both are locally integrable on `Ω` and `∂^v f = g` as distributions on
`Ω`, that is, `∫ φ g = (-1)^k ∫ (∂^v φ) f` for every smooth compactly supported `φ` in `Ω`
(`Rd.hasWeakLineDeriv_iff_integral`). -/
structure HasWeakLineDeriv (Ω : Opens V) {k : ℕ} (v : Fin k → V) (f g : V → ℂ) : Prop where
  /-- `f` is locally integrable on `Ω`. -/
  locallyIntegrableOn : LocallyIntegrableOn f Ω volume
  /-- `g` is locally integrable on `Ω`. -/
  locallyIntegrableOn_deriv : LocallyIntegrableOn g Ω volume
  /-- `∂^v f = g` as distributions on `Ω`. -/
  eq : ∂^{v} (Distribution.ofFun Ω f volume ⊤) = Distribution.ofFun Ω g volume ⊤

/-- The **Sobolev space** `W^m_p(Ω)` as a predicate: `f ∈ L_p(Ω)`, and for every order `k ≤ m`
and all directions `v = (v_0, …, v_{k-1})` the weak derivative `∂^v f` exists on `Ω` and lies in
`L_p(Ω)`. -/
def MemWeakSobolev (Ω : Opens V) (m : ℕ) (p : ℝ≥0∞) (f : V → ℂ) : Prop :=
  MemLp f p (volume.restrict Ω) ∧ ∀ k ≤ m, ∀ v : Fin k → V,
    ∃ g : V → ℂ, MemLp g p (volume.restrict Ω) ∧ HasWeakLineDeriv Ω v f g

/-- The **Sobolev space** `W^m_p(V)` as a predicate on `f ∈ L_p(V)`: the case `Ω = V` of
`Rd.MemWeakSobolev`. -/
def MemSobolev {p : ℝ≥0∞} (m : ℕ) (f : Lp ℂ p (volume : Measure V)) : Prop :=
  MemWeakSobolev ⊤ m p f

/-- Lebesgue measure restricted to the whole space `Ω = V` is Lebesgue measure, so that
`L_p(Ω) = L_p(V)` for `Ω = V`; a rewrite form of Mathlib's simp lemmas `Opens.coe_top` and
`Measure.restrict_univ`. -/
theorem volume_restrict_top : (volume : Measure V).restrict ((⊤ : Opens V) : Set V) = volume := by
  simp

/-- A function in `L_p(Ω)`, `1 ≤ p`, is locally integrable on `Ω`. -/
theorem locallyIntegrableOn_of_memLp {Ω : Opens V} {p : ℝ≥0∞} (hp : 1 ≤ p) {f : V → ℂ}
    (hf : MemLp f p (volume.restrict Ω)) : LocallyIntegrableOn f Ω volume :=
  locallyIntegrableOn_of_locallyIntegrable_restrict (hf.locallyIntegrable hp)

variable {Ω Ω' : Opens V} {k : ℕ} {v : Fin k → V} {f f' g g' : V → ℂ}

/-- The integral form of a weak derivative: if `g = ∂^v f` weakly on `Ω`, then
`∫ φ g = (-1)^k ∫ (∂^v φ) f` for every test function `φ` on `Ω`. -/
theorem HasWeakLineDeriv.integral_eq (h : HasWeakLineDeriv Ω v f g) (φ : 𝓓(Ω, ℝ)) :
    ∫ x, φ x • g x = (-1 : ℝ) ^ k • ∫ x, (∂^{v} φ) x • f x := by
  have h' := DFunLike.congr_fun h.eq φ
  rw [Distribution.iteratedLineDerivOp_apply_apply, Distribution.ofFun_apply h.1,
    Distribution.ofFun_apply h.2] at h'
  exact h'.symm

/-- **Weak derivatives by integration by parts**: for locally integrable `f`, `g` on `Ω`, `g` is
the weak derivative `∂^v f` on `Ω` iff `∫ φ g = (-1)^k ∫ (∂^v φ) f` for every test function `φ`
on `Ω`. -/
theorem hasWeakLineDeriv_iff_integral (hf : LocallyIntegrableOn f Ω volume)
    (hg : LocallyIntegrableOn g Ω volume) :
    HasWeakLineDeriv Ω v f g ↔
      ∀ φ : 𝓓(Ω, ℝ), ∫ x, φ x • g x = (-1 : ℝ) ^ k • ∫ x, (∂^{v} φ) x • f x := by
  refine ⟨fun h => h.integral_eq, fun h => ⟨hf, hg, ?_⟩⟩
  ext φ
  rw [Distribution.iteratedLineDerivOp_apply_apply, Distribution.ofFun_apply hf,
    Distribution.ofFun_apply hg, h φ]

/-- The weak derivative is **unique** almost everywhere on `Ω`. -/
theorem HasWeakLineDeriv.unique (h : HasWeakLineDeriv Ω v f g) (h' : HasWeakLineDeriv Ω v f g') :
    g =ᵐ[volume.restrict Ω] g' :=
  Distribution.ofFun_injective h.2 h'.2 (h.eq.symm.trans h'.eq)

/-- **Weak derivatives on `V` are unique classes**: two weak derivatives `G`, `G' ∈ L_r(V)` of the
same function on the whole space `V` are equal in `L_r(V)` (`Rd.HasWeakLineDeriv.unique`). -/
theorem HasWeakLineDeriv.eq_of_top {r : ℝ≥0∞} {G G' : Lp ℂ r (volume : Measure V)}
    (h : HasWeakLineDeriv ⊤ v f G) (h' : HasWeakLineDeriv ⊤ v f G') : G = G' := by
  have hu := h.unique h'
  rw [volume_restrict_top] at hu
  exact Lp.ext hu

/-- The derivative of order zero: a locally integrable `f` is its own weak derivative along the
empty family of directions. -/
theorem hasWeakLineDeriv_fin_zero (v : Fin 0 → V) (hf : LocallyIntegrableOn f Ω volume) :
    HasWeakLineDeriv Ω v f f :=
  ⟨hf, hf, LineDeriv.iteratedLineDerivOp_fin_zero v _⟩

/-- The weak derivative of the zero function is zero. -/
theorem hasWeakLineDeriv_zero : HasWeakLineDeriv Ω v (0 : V → ℂ) 0 := by
  refine ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, ?_⟩
  rw [Distribution.ofFun_zero, LineDeriv.iteratedLineDerivOp_zero]

/-- Weak derivatives are additive: `∂^v (f + f') = ∂^v f + ∂^v f'`. -/
theorem HasWeakLineDeriv.add (h : HasWeakLineDeriv Ω v f g) (h' : HasWeakLineDeriv Ω v f' g') :
    HasWeakLineDeriv Ω v (f + f') (g + g') := by
  refine ⟨h.1.add h'.1, h.2.add h'.2, ?_⟩
  rw [Distribution.ofFun_add h.1 h'.1, Distribution.ofFun_add h.2 h'.2,
    LineDeriv.iteratedLineDerivOp_add, h.eq, h'.eq]

/-- The weak derivative of `-f` is `-∂^v f`. -/
theorem HasWeakLineDeriv.neg (h : HasWeakLineDeriv Ω v f g) : HasWeakLineDeriv Ω v (-f) (-g) := by
  refine ⟨h.1.neg, h.2.neg, ?_⟩
  rw [Distribution.ofFun_neg, Distribution.ofFun_neg, LineDeriv.iteratedLineDerivOp_neg, h.eq]

/-- Weak derivatives of differences: `∂^v (f - f') = ∂^v f - ∂^v f'`. -/
theorem HasWeakLineDeriv.sub (h : HasWeakLineDeriv Ω v f g) (h' : HasWeakLineDeriv Ω v f' g') :
    HasWeakLineDeriv Ω v (f - f') (g - g') := by
  simpa only [sub_eq_add_neg] using h.add h'.neg

/-- Weak derivatives are homogeneous: `∂^v (c f) = c ∂^v f` for `c ∈ ℂ`. -/
theorem HasWeakLineDeriv.smul (h : HasWeakLineDeriv Ω v f g) (c : ℂ) :
    HasWeakLineDeriv Ω v (c • f) (c • g) := by
  refine (hasWeakLineDeriv_iff_integral (h.1.smul c) (h.2.smul c)).2 fun φ => ?_
  have hc : ∀ (w : V → ℝ) (u : V → ℂ), ∫ x, w x • (c • u) x = c • ∫ x, w x • u x := by
    intro w u
    rw [← integral_smul]
    exact integral_congr_ae (ae_of_all _ fun x => smul_comm (w x) c (u x))
  rw [hc, hc, h.integral_eq φ, smul_comm]

/-- **Weak derivatives of finite sums**: if `G_j` is the weak derivative `∂^v F_j` on `Ω` for
every `j ∈ s`, `s` finite, then `∑_{j ∈ s} G_j` is the weak derivative of `∑_{j ∈ s} F_j`
(`Rd.HasWeakLineDeriv.add`, by induction on `s`). -/
theorem HasWeakLineDeriv.sum {ι : Type*} {s : Finset ι} {F G : ι → V → ℂ}
    (h : ∀ j ∈ s, HasWeakLineDeriv Ω v (F j) (G j)) :
    HasWeakLineDeriv Ω v (∑ j ∈ s, F j) (∑ j ∈ s, G j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (hasWeakLineDeriv_zero : HasWeakLineDeriv Ω v 0 0)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- Weak derivatives only see `f` and `g` almost everywhere on `Ω`. -/
theorem HasWeakLineDeriv.congr_ae (h : HasWeakLineDeriv Ω v f g)
    (hf : f =ᵐ[volume.restrict Ω] f') (hg : g =ᵐ[volume.restrict Ω] g') :
    HasWeakLineDeriv Ω v f' g' := by
  refine ⟨h.1.congr hf, h.2.congr hg, ?_⟩
  rw [← Distribution.ofFun_congr_ae hf, ← Distribution.ofFun_congr_ae hg]
  exact h.eq

/-- **Weak derivatives are local**: a weak derivative on `Ω` is one on every open `Ω' ⊆ Ω`,
because a test function on `Ω'` is one on `Ω` (Mathlib's `TestFunction.monoCLM`). -/
theorem HasWeakLineDeriv.mono (h : HasWeakLineDeriv Ω v f g) (hΩ : Ω' ≤ Ω) :
    HasWeakLineDeriv Ω' v f g := by
  have hs : (Ω' : Set V) ⊆ Ω := hΩ
  refine (hasWeakLineDeriv_iff_integral (h.1.mono_set hs) (h.2.mono_set hs)).2 fun φ => ?_
  have hφ : ((TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ)) : V → ℝ) = φ := by
    simp [hΩ]
  have h' := h.integral_eq (TestFunction.monoCLM ℝ φ)
  rwa [coe_iteratedLineDerivOp_eq hφ, hφ] at h'

/-- A function with a weak derivative on the whole space `V` is locally integrable on `V`. -/
theorem HasWeakLineDeriv.locallyIntegrable (h : HasWeakLineDeriv ⊤ v f g) :
    LocallyIntegrable f volume := by
  have h' := h.locallyIntegrableOn
  rwa [Opens.coe_top, locallyIntegrableOn_univ] at h'

/-- A weak derivative on the whole space `V` is locally integrable on `V`. -/
theorem HasWeakLineDeriv.locallyIntegrable_deriv (h : HasWeakLineDeriv ⊤ v f g) :
    LocallyIntegrable g volume := by
  have h' := h.locallyIntegrableOn_deriv
  rwa [Opens.coe_top, locallyIntegrableOn_univ] at h'

/-- **Weak derivatives of weak derivatives**: if `G = ∂^v f` and `H = ∂^{(w, v)} f` weakly on `Ω`,
then `H = ∂_w G` weakly on `Ω`, since `∂^{(w, v)} = ∂_w ∂^v` for distributions (Mathlib's
`LineDeriv.iteratedLineDerivOp_succ_left`). -/
theorem HasWeakLineDeriv.of_cons {w : V} {G H : V → ℂ} (h : HasWeakLineDeriv Ω v f G)
    (h' : HasWeakLineDeriv Ω (Fin.cons w v) f H) :
    HasWeakLineDeriv Ω (fun _ : Fin 1 => w) G H := by
  refine ⟨h.locallyIntegrableOn_deriv, h'.locallyIntegrableOn_deriv, ?_⟩
  rw [LineDeriv.iteratedLineDerivOp_one, ← h'.eq,
    LineDeriv.iteratedLineDerivOp_succ_left (Fin.cons w v), Fin.cons_zero, Fin.tail_cons, h.eq]

/-- **Weak derivatives vanish where the function vanishes**: if `g` is a weak derivative `∂^v f`
on `Ω`, `O ⊆ Ω` is open and `f = 0` almost everywhere on `O`, then `g = 0` almost everywhere on
`O`, by locality (`Rd.HasWeakLineDeriv.mono`) and uniqueness (`Rd.HasWeakLineDeriv.unique`). -/
theorem HasWeakLineDeriv.ae_eq_zero_of_ae_eq_zero {O : Opens V} (h : HasWeakLineDeriv Ω v f g)
    (hO : O ≤ Ω) (hf : f =ᵐ[volume.restrict (O : Set V)] 0) :
    g =ᵐ[volume.restrict (O : Set V)] 0 :=
  ((h.mono hO).congr_ae hf EventuallyEq.rfl).unique hasWeakLineDeriv_zero

/-- **The integral form with complex test functions**: if `g = ∂^v f` weakly on `Ω`, then
`∫ w g = (-1)^k ∫ (∂^v w) f` for every smooth compactly supported complex `w` (a Schwartz function)
with `tsupport w ⊆ Ω`, by splitting `w = Re w + i Im w` into real test functions
(`Rd.exists_testSchwartz_eq_of_tsupport_subset`). -/
theorem HasWeakLineDeriv.integral_mul_eq (h : HasWeakLineDeriv Ω v f g) (w : 𝓢(V, ℂ))
    (hw : HasCompactSupport w) (hwΩ : tsupport w ⊆ Ω) :
    ∫ x, w x * g x = (-1 : ℂ) ^ k * ∫ x, (∂^{v} w : 𝓢(V, ℂ)) x * f x := by
  obtain ⟨a, b, rfl⟩ := exists_testSchwartz_eq_of_tsupport_subset w hw hwΩ
  have hc : ∀ (φ : 𝓓(Ω, ℝ)) (u : V → ℂ), (fun x => ((φ x : ℝ) : ℂ) * u x) =
      fun x => φ x • u x := fun φ u => funext fun x => (Complex.real_smul ..).symm
  have hsplit : ∀ (φ ψ : 𝓓(Ω, ℝ)) (u : V → ℂ), LocallyIntegrableOn u Ω volume →
      ∫ x, (testSchwartz φ + Complex.I • testSchwartz ψ) x * u x =
        (∫ x, φ x • u x) + Complex.I * ∫ x, ψ x • u x := fun φ ψ u hu => by
    have h1 := φ.integrable_smul hu
    have h2 := (ψ.integrable_smul hu).const_mul Complex.I
    rw [← integral_const_mul, ← integral_add h1 h2]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [add_apply, smul_apply, testSchwartz_apply, smul_eq_mul,
      Complex.real_smul]
    ring
  rw [LineDeriv.iteratedLineDerivOp_add, LineDeriv.iteratedLineDerivOp_smul,
    iteratedLineDerivOp_testSchwartz, iteratedLineDerivOp_testSchwartz, hsplit a b g h.2,
    hsplit _ _ f h.1, h.integral_eq a, h.integral_eq b]
  simp only [Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]
  ring

/-- The product `φ χ` of a real test function `φ` on `Ω` with a smooth real function `χ` is a test
function on `Ω`. -/
noncomputable def testFunctionMul (φ : 𝓓(Ω, ℝ)) {χ : V → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) : 𝓓(Ω, ℝ) :=
  ⟨fun x => φ x * χ x, φ.contDiff.mul hχ, φ.hasCompactSupport.mul_right,
    (tsupport_mul_subset_left).trans φ.tsupport_subset⟩

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The values of `Rd.testFunctionMul`: `(φ χ)(x) = φ(x) χ(x)`. -/
theorem testFunctionMul_apply (φ : 𝓓(Ω, ℝ)) {χ : V → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (x : V) :
    testFunctionMul φ hχ x = φ x * χ x :=
  rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The product rule for test functions**: `∂_w (φ χ) = (∂_w φ) χ + φ ∂_w χ`. -/
theorem lineDerivOp_testFunctionMul_apply (φ : 𝓓(Ω, ℝ)) {χ : V → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (w x : V) :
    (∂_{w} (testFunctionMul φ hχ)) x = (∂_{w} φ) x * χ x + φ x * fderiv ℝ χ x w := by
  have hφ : DifferentiableAt ℝ φ x := (φ.contDiff.differentiable (by simp)).differentiableAt
  have hχx : DifferentiableAt ℝ χ x := (hχ.differentiable (by simp)).differentiableAt
  rw [lineDerivOp_testFunction_apply, lineDerivOp_testFunction_apply]
  change fderiv ℝ (fun y => φ y * χ y) x w = _
  rw [fderiv_fun_mul hφ hχx]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

section Cutoff

variable {O B : Opens V}

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The product `φ χ` of a real test function `φ` on `O` with a smooth real function `χ` whose
closed support lies in `B` is a test function on `O ∩ B`. -/
noncomputable def testFunctionMulOn (φ : 𝓓(O, ℝ)) {χ : V → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχB : tsupport χ ⊆ B) : 𝓓(O ⊓ B, ℝ) :=
  ⟨fun x => φ x * χ x, φ.contDiff.mul hχ, φ.hasCompactSupport.mul_right, by
    rw [Opens.coe_inf]
    exact Set.subset_inter ((tsupport_mul_subset_left).trans φ.tsupport_subset)
      ((tsupport_mul_subset_right).trans hχB)⟩

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The values of `Rd.testFunctionMulOn`: `(φ χ)(x) = φ(x) χ(x)`. -/
theorem testFunctionMulOn_apply (φ : 𝓓(O, ℝ)) {χ : V → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχB : tsupport χ ⊆ B) (x : V) :
    testFunctionMulOn φ hχ hχB x = φ x * χ x :=
  rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The product rule for `Rd.testFunctionMulOn`**: `∂_w (φ χ) = (∂_w φ) χ + φ ∂_w χ`. As a
function, `φ χ` is the test function `Rd.testFunctionMul φ` on `O`, whose derivative is
`Rd.lineDerivOp_testFunctionMul_apply`. -/
theorem lineDerivOp_testFunctionMulOn_apply (φ : 𝓓(O, ℝ)) {χ : V → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχB : tsupport χ ⊆ B) (w x : V) :
    (∂_{w} (testFunctionMulOn φ hχ hχB)) x = (∂_{w} φ) x * χ x + φ x * fderiv ℝ χ x w := by
  rw [lineDerivOp_testFunction_apply]
  exact (lineDerivOp_testFunction_apply (testFunctionMul φ hχ) w x).symm.trans
    (lineDerivOp_testFunctionMul_apply φ hχ w x)

/-- **Cutoff products are locally integrable on the larger set**: if `u` is locally integrable
on `O ∩ B` and `c` is continuous with closed support in `B`, then `c u` is locally integrable on
`O`; near points of `B` this is the product with a continuous function, and near the other points
of `O`, `c u` vanishes. -/
theorem locallyIntegrableOn_mul_of_tsupport_subset {u : V → ℂ}
    (hu : LocallyIntegrableOn u (O ⊓ B : Opens V) volume) {c : V → ℂ} (hc : Continuous c)
    (hcB : tsupport c ⊆ B) : LocallyIntegrableOn (fun x => c x * u x) O volume := by
  intro x hx
  rw [nhdsWithin_eq_nhds.2 (O.isOpen.mem_nhds hx)]
  by_cases hxB : x ∈ (B : Set V)
  · have hxOB : x ∈ ((O ⊓ B : Opens V) : Set V) := by
      rw [Opens.coe_inf]
      exact ⟨hx, hxB⟩
    have h := hu.continuousOn_mul hc.continuousOn (O ⊓ B).isOpen.isLocallyClosed x hxOB
    rwa [nhdsWithin_eq_nhds.2 ((O ⊓ B).isOpen.mem_nhds hxOB)] at h
  · have hx' : x ∉ tsupport c := fun h => hxB (hcB h)
    refine ⟨(tsupport c)ᶜ, (isClosed_tsupport c).isOpen_compl.mem_nhds hx', ?_⟩
    refine integrableOn_zero.congr_fun (fun y hy => ?_)
      (isClosed_tsupport c).isOpen_compl.measurableSet
    simp [image_eq_zero_of_notMem_tsupport hy]

/-- **The product rule with a cutoff**: if `g = ∂_w f` weakly on `O ∩ B` and `χ` is a smooth
real function with closed support in `B`, then `χ g + (∂_w χ) f = ∂_w (χ f)` weakly on `O`. Tested
against `φ ∈ 𝓓(O)`, this is the weak derivative on `O ∩ B` tested against the test function
`φ χ` (`Rd.testFunctionMulOn`, `Rd.lineDerivOp_testFunctionMulOn_apply`). -/
theorem HasWeakLineDeriv.mul_of_tsupport_subset {w : V} {f g : V → ℂ}
    (h : HasWeakLineDeriv (O ⊓ B) (fun _ : Fin 1 => w) f g) {χ : V → ℝ}
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (hχB : tsupport χ ⊆ B) :
    HasWeakLineDeriv O (fun _ : Fin 1 => w) (fun x => (χ x : ℂ) * f x)
      (fun x => (χ x : ℂ) * g x + (fderiv ℝ χ x w : ℂ) * f x) := by
  have hχ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x => fderiv ℝ χ x w :=
    (hχ.fderiv_right (by simp)).clm_apply contDiff_const
  have hχ'B : tsupport (fun x => fderiv ℝ χ x w) ⊆ B := (tsupport_fderiv_apply_subset ℝ w).trans hχB
  have hc : Continuous fun x => (χ x : ℂ) := Complex.continuous_ofReal.comp hχ.continuous
  have hc' : Continuous fun x => (fderiv ℝ χ x w : ℂ) :=
    Complex.continuous_ofReal.comp hχ'.continuous
  have hcB : tsupport (fun x => (χ x : ℂ)) ⊆ B :=
    (tsupport_comp_subset Complex.ofReal_zero χ).trans hχB
  have hcB' : tsupport (fun x => (fderiv ℝ χ x w : ℂ)) ⊆ B :=
    (tsupport_comp_subset Complex.ofReal_zero _).trans hχ'B
  refine (hasWeakLineDeriv_iff_integral (locallyIntegrableOn_mul_of_tsupport_subset h.1 hc hcB)
    ((locallyIntegrableOn_mul_of_tsupport_subset h.2 hc hcB).add
      (locallyIntegrableOn_mul_of_tsupport_subset h.1 hc' hcB'))).2 fun φ => ?_
  have h1 := h.integral_eq (testFunctionMulOn φ hχ hχB)
  have i1 := (testFunctionMulOn φ hχ hχB).integrable_smul h.2
  have i2 := (testFunctionMulOn φ hχ' hχ'B).integrable_smul h.1
  have i3 := (testFunctionMulOn (∂_{w} φ) hχ hχB).integrable_smul h.1
  rw [LineDeriv.iteratedLineDerivOp_one] at h1 ⊢
  have e1 : (fun x => φ x • ((χ x : ℂ) * g x + (fderiv ℝ χ x w : ℂ) * f x)) =
      fun x => testFunctionMulOn φ hχ hχB x • g x + testFunctionMulOn φ hχ' hχ'B x • f x :=
    funext fun x => by
      simp only [testFunctionMulOn_apply, Complex.real_smul, Complex.ofReal_mul]
      ring
  have e2 : (fun x => (∂_{w} (testFunctionMulOn φ hχ hχB)) x • f x) =
      fun x => testFunctionMulOn (∂_{w} φ) hχ hχB x • f x + testFunctionMulOn φ hχ' hχ'B x • f x :=
    funext fun x => by
      simp only [lineDerivOp_testFunctionMulOn_apply, testFunctionMulOn_apply, Complex.real_smul,
        Complex.ofReal_mul, Complex.ofReal_add]
      ring
  have e3 : (fun x => (∂_{w} φ) x • ((χ x : ℂ) * f x)) =
      fun x => testFunctionMulOn (∂_{w} φ) hχ hχB x • f x := funext fun x => by
    simp only [testFunctionMulOn_apply, Complex.real_smul, Complex.ofReal_mul]
    ring
  simp only [Pi.add_apply]
  rw [e1, integral_add i1 i2, h1, e2, integral_add i3 i2, e3]
  simp only [pow_one, neg_one_smul]
  abel

end Cutoff

/-- **The product rule for weak derivatives**: if `g = ∂_w f` weakly on `Ω` and `χ` is a smooth
real function, then `χ g + (∂_w χ) f = ∂_w (χ f)` weakly on `Ω`: the product rule with a cutoff
(`Rd.HasWeakLineDeriv.mul_of_tsupport_subset`) for `B = V`. -/
theorem HasWeakLineDeriv.mul_contDiff {w : V} (h : HasWeakLineDeriv Ω (fun _ : Fin 1 => w) f g)
    {χ : V → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) :
    HasWeakLineDeriv Ω (fun _ : Fin 1 => w) (fun x => (χ x : ℂ) * f x)
      (fun x => (χ x : ℂ) * g x + (fderiv ℝ χ x w : ℂ) * f x) := by
  have h' : HasWeakLineDeriv (Ω ⊓ ⊤) (fun _ : Fin 1 => w) f g := by rwa [inf_top_eq]
  exact h'.mul_of_tsupport_subset hχ (by simp)

/-! ### Sobolev spaces on open sets -/

/-- `W^0_p(Ω) = L_p(Ω)` for `1 ≤ p`. -/
theorem memWeakSobolev_zero_iff {p : ℝ≥0∞} (hp : 1 ≤ p) :
    MemWeakSobolev Ω 0 p f ↔ MemLp f p (volume.restrict Ω) := by
  refine ⟨fun h => h.1, fun h => ⟨h, fun k hk v => ?_⟩⟩
  obtain rfl : k = 0 := Nat.le_zero.1 hk
  exact ⟨f, h, hasWeakLineDeriv_fin_zero v (locallyIntegrableOn_of_memLp hp h)⟩

/-- `W^m_p(Ω) ⊆ W^n_p(Ω)` for `n ≤ m`. -/
theorem MemWeakSobolev.mono_order {p : ℝ≥0∞} {m n : ℕ} (hf : MemWeakSobolev Ω m p f)
    (hnm : n ≤ m) : MemWeakSobolev Ω n p f :=
  ⟨hf.1, fun k hk v => hf.2 k (hk.trans hnm) v⟩

/-- Restriction to a smaller open set: `f ∈ W^m_p(Ω)` gives `f ∈ W^m_p(Ω')` for `Ω' ⊆ Ω`. -/
theorem MemWeakSobolev.mono_set {p : ℝ≥0∞} {m : ℕ} (hf : MemWeakSobolev Ω m p f)
    (hΩ : Ω' ≤ Ω) : MemWeakSobolev Ω' m p f := by
  have hμ : volume.restrict (Ω' : Set V) ≤ volume.restrict Ω :=
    Measure.restrict_mono (show (Ω' : Set V) ⊆ Ω from hΩ) le_rfl
  refine ⟨hf.1.mono_measure hμ, fun k hk v => ?_⟩
  obtain ⟨g, hg, hfg⟩ := hf.2 k hk v
  exact ⟨g, hg.mono_measure hμ, hfg.mono hΩ⟩

/-- The zero function lies in `W^m_p(Ω)`. -/
theorem zero_memWeakSobolev {p : ℝ≥0∞} {m : ℕ} : MemWeakSobolev Ω m p 0 :=
  ⟨MemLp.zero, fun _ _ _ => ⟨0, MemLp.zero, hasWeakLineDeriv_zero⟩⟩

/-- `W^m_p(Ω)` is closed under addition. -/
theorem MemWeakSobolev.add {p : ℝ≥0∞} {m : ℕ} (hf : MemWeakSobolev Ω m p f)
    (hf' : MemWeakSobolev Ω m p f') : MemWeakSobolev Ω m p (f + f') := by
  refine ⟨hf.1.add hf'.1, fun k hk v => ?_⟩
  obtain ⟨g, hg, hfg⟩ := hf.2 k hk v
  obtain ⟨g', hg', hfg'⟩ := hf'.2 k hk v
  exact ⟨g + g', hg.add hg', hfg.add hfg'⟩

/-- `W^m_p(Ω)` is closed under multiplication by complex scalars. -/
theorem MemWeakSobolev.smul {p : ℝ≥0∞} {m : ℕ} (hf : MemWeakSobolev Ω m p f) (c : ℂ) :
    MemWeakSobolev Ω m p (c • f) := by
  refine ⟨hf.1.const_smul c, fun k hk v => ?_⟩
  obtain ⟨g, hg, hfg⟩ := hf.2 k hk v
  exact ⟨c • g, hg.const_smul c, hfg.smul c⟩

/-- `W^m_p(Ω)` only sees `f` almost everywhere on `Ω`: if `f ∈ W^m_p(Ω)` and `f = f'` almost
everywhere on `Ω`, then `f' ∈ W^m_p(Ω)`; the weak derivatives of `f` serve for `f'`
(`Rd.HasWeakLineDeriv.congr_ae`). -/
theorem MemWeakSobolev.congr_ae {p : ℝ≥0∞} {m : ℕ} (hf : MemWeakSobolev Ω m p f)
    (hff' : f =ᵐ[volume.restrict Ω] f') : MemWeakSobolev Ω m p f' := by
  refine ⟨MemLp.ae_eq hff' hf.1, fun k hk v => ?_⟩
  obtain ⟨g, hg, hfg⟩ := hf.2 k hk v
  exact ⟨g, hg, hfg.congr_ae hff' Filter.EventuallyEq.rfl⟩

/-- The zero class lies in `W^m_p(V)`. -/
theorem zero_memSobolev {p : ℝ≥0∞} {m : ℕ} : MemSobolev m (0 : Lp ℂ p (volume : Measure V)) :=
  zero_memWeakSobolev.congr_ae (ae_restrict_of_ae (Lp.coeFn_zero ..).symm)

/-- `W^m_p(V)` is closed under addition in `L_p(V)`. -/
theorem MemSobolev.add {p : ℝ≥0∞} {m : ℕ} {F G : Lp ℂ p (volume : Measure V)}
    (hF : MemSobolev m F) (hG : MemSobolev m G) : MemSobolev m (F + G) :=
  (MemWeakSobolev.add hF hG).congr_ae (ae_restrict_of_ae (Lp.coeFn_add F G).symm)

/-- `W^m_p(V)` is closed under multiplication by complex scalars in `L_p(V)`. -/
theorem MemSobolev.smul {p : ℝ≥0∞} {m : ℕ} {F : Lp ℂ p (volume : Measure V)}
    (hF : MemSobolev m F) (c : ℂ) : MemSobolev m (c • F) :=
  (MemWeakSobolev.smul hF c).congr_ae (ae_restrict_of_ae (Lp.coeFn_smul c F).symm)

/-- `W^m_p(V)` is closed under finite sums in `L_p(V)` (`Rd.MemSobolev.add`). -/
theorem MemSobolev.sum {p : ℝ≥0∞} {m : ℕ} {ι : Type*} (s : Finset ι)
    {F : ι → Lp ℂ p (volume : Measure V)} (hF : ∀ i ∈ s, MemSobolev m (F i)) :
    MemSobolev m (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero_memSobolev : MemSobolev m (0 : Lp ℂ p (volume : Measure V)))
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

/-- **`W^m_p(V)` with derivatives in `L_p(V)`**: `f ∈ L_p(V)` lies in `W^m_p(V)` iff for every
order `k ≤ m` and all directions `v ∈ V^k` some class `g ∈ L_p(V)` is the weak derivative
`∂^v f` on `V`. -/
theorem memSobolev_iff_exists_hasWeakLineDeriv {p : ℝ≥0∞} {m : ℕ}
    (f : Lp ℂ p (volume : Measure V)) :
    MemSobolev m f ↔ ∀ k ≤ m, ∀ v : Fin k → V,
      ∃ g : Lp ℂ p (volume : Measure V), HasWeakLineDeriv ⊤ v f g := by
  constructor
  · rintro ⟨-, h⟩ k hk v
    obtain ⟨g, hg, hfg⟩ := h k hk v
    rw [volume_restrict_top] at hg
    refine ⟨hg.toLp g, hfg.congr_ae EventuallyEq.rfl ?_⟩
    rw [volume_restrict_top]
    exact hg.coeFn_toLp.symm
  · intro h
    refine ⟨by simpa using Lp.memLp f, fun k hk v => ?_⟩
    obtain ⟨g, hg⟩ := h k hk v
    exact ⟨g, by simpa using Lp.memLp g, hg⟩

/-! ### Limits -/

/-- **Hölder bound for the pairing with a test function**: for `1 ≤ p`, a test function `φ` on
`Ω` with support `K` and every `h` a.e. strongly measurable on `Ω`,
`‖φ h‖_{L_1(Ω)} ≤ ‖φ‖_∞ |K|^(1 - 1/p) ‖h‖_{L_p(Ω)}` (Hölder on the compact set `K`: Mathlib's
`eLpNorm_le_eLpNorm_mul_rpow_measure_univ` and `eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm`). -/
theorem eLpNorm_testFunction_smul_le {p : ℝ≥0∞} (hp : 1 ≤ p) (φ : 𝓓(Ω, ℝ)) {h : V → ℂ}
    (hh : AEStronglyMeasurable h (volume.restrict Ω)) :
    eLpNorm (fun x => φ x • h x) 1 (volume.restrict Ω) ≤
      eLpNorm φ ∞ volume * volume (tsupport φ) ^ (1 - 1 / p.toReal) *
        eLpNorm h p (volume.restrict Ω) := by
  set μ := volume.restrict (Ω : Set V)
  have hm : AEStronglyMeasurable (fun x => φ x • h x) μ := φ.continuous.aestronglyMeasurable.smul hh
  have hsupp : (Function.support fun x => φ x • h x) ⊆ tsupport φ := fun x hx =>
    subset_tsupport _ fun h0 => hx (by simp [h0])
  calc eLpNorm (fun x => φ x • h x) 1 μ
      = eLpNorm (fun x => φ x • h x) 1 (μ.restrict (tsupport φ)) :=
        (eLpNorm_restrict_eq_of_support_subset hm hsupp).symm
    _ ≤ eLpNorm (fun x => φ x • h x) p (μ.restrict (tsupport φ)) *
          (μ.restrict (tsupport φ)) Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hm.restrict
    _ ≤ (eLpNorm φ ∞ volume * eLpNorm h p μ) * volume (tsupport φ) ^ (1 - 1 / p.toReal) := by
        gcongr
        · calc eLpNorm (fun x => φ x • h x) p (μ.restrict (tsupport φ))
              ≤ eLpNorm φ ∞ (μ.restrict (tsupport φ)) * eLpNorm h p (μ.restrict (tsupport φ)) :=
                eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm p φ.continuous.aestronglyMeasurable
            _ ≤ eLpNorm φ ∞ volume * eLpNorm h p μ := by
                gcongr
                · exact Measure.restrict_le_self.trans Measure.restrict_le_self
                · exact Measure.restrict_le_self
        · rw [Measure.restrict_apply_univ, ENNReal.toReal_one, div_one]
          exact ENNReal.rpow_le_rpow (Measure.restrict_apply_le _ _)
            (one_sub_one_div_toReal_nonneg hp)
    _ = _ := by ring

/-- If `‖h_i - h‖_{L_p(μ)} → 0` and `h ∈ L_p(μ)`, then eventually every `h_i` lies in `L_p(μ)`:
`h_i = (h_i - h) + h` with `‖h_i - h‖_p < 1` eventually. -/
theorem eventually_memLp_of_tendsto {α : Type*} [MeasurableSpace α] {p : ℝ≥0∞} {μ : Measure α}
    {ι : Type*} {l : Filter ι} {hs : ι → α → ℂ} {h : α → ℂ} (hh : MemLp h p μ)
    (hlim : Tendsto (fun i => eLpNorm (hs i - h) p μ) l (𝓝 0)) : ∀ᶠ i in l, MemLp (hs i) p μ := by
  filter_upwards [hlim.eventually (gt_mem_nhds zero_lt_one)] with i hi
  have hd : MemLp (hs i - h) p μ := memLp_iff.2 (hi.trans ENNReal.one_lt_top)
  simpa using hd.add hh

/-- **Convergence in `L_p(Ω)` gives convergence of the pairings with a test function**: if
`h_i → h` in `L_p(Ω)`, `1 ≤ p`, with `h ∈ L_p(Ω)` and `h_i ∈ L_p(Ω)` eventually, then
`∫ φ h_i → ∫ φ h` for every test function `φ` on `Ω`. -/
theorem tendsto_integral_testFunction_smul {p : ℝ≥0∞} (hp : 1 ≤ p) (φ : 𝓓(Ω, ℝ)) {ι : Type*}
    {l : Filter ι} {hs : ι → V → ℂ} {h : V → ℂ}
    (hhs : ∀ᶠ i in l, MemLp (hs i) p (volume.restrict Ω))
    (hh : MemLp h p (volume.restrict Ω))
    (hlim : Tendsto (fun i => eLpNorm (hs i - h) p (volume.restrict Ω)) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, φ x • hs i x) l (𝓝 (∫ x, φ x • h x)) := by
  have hcompl : ∀ u : V → ℂ, ∫ x in (Ω : Set V), φ x • u x = ∫ x, φ x • u x := fun u =>
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      simp [φ.zero_on_compl hx]
  simp only [← hcompl]
  refine tendsto_integral_of_L1' _ (hhs.mono fun i hi =>
    (φ.integrable_smul (locallyIntegrableOn_of_memLp hp hi)).restrict) ?_
  have hC : eLpNorm φ ∞ volume * volume (tsupport φ) ^ (1 - 1 / p.toReal) ≠ ∞ :=
    ENNReal.mul_ne_top (φ.memLp_top).eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (one_sub_one_div_toReal_nonneg hp)
        φ.hasCompactSupport.isCompact.measure_ne_top)
  have hlim' := ENNReal.Tendsto.const_mul hlim (Or.inr hC)
  rw [mul_zero] at hlim'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim'
    (Eventually.of_forall fun _ => bot_le) (hhs.mono fun i hi => ?_)
  have he : ((fun x => φ x • hs i x) - fun x => φ x • h x) = fun x => φ x • (hs i - h) x := by
    funext x
    simp [smul_sub]
  simp only [he]
  exact eLpNorm_testFunction_smul_le hp φ (hi.aestronglyMeasurable.sub hh.aestronglyMeasurable)

/-- **Weak derivatives pass to limits in `L_p(Ω)`**: if `g_i = ∂^v f_i` weakly on `Ω`,
`f ∈ L_p(Ω)`, `g ∈ L_r(Ω)`, `‖f_i - f‖_{L_p(Ω)} → 0` and `‖g_i - g‖_{L_r(Ω)} → 0` with
`1 ≤ p, r`, along a nontrivial filter, then `g = ∂^v f` weakly on `Ω`. Eventually the `f_i`
lie in `L_p(Ω)` and the `g_i` in `L_r(Ω)` (`Rd.eventually_memLp_of_tendsto`). -/
theorem HasWeakLineDeriv.of_tendsto {p r : ℝ≥0∞} (hp : 1 ≤ p) (hr : 1 ≤ r) {ι : Type*}
    {l : Filter ι} [l.NeBot] {fs gs : ι → V → ℂ} (h : ∀ i, HasWeakLineDeriv Ω v (fs i) (gs i))
    (hf : MemLp f p (volume.restrict Ω)) (hg : MemLp g r (volume.restrict Ω))
    (hlf : Tendsto (fun i => eLpNorm (fs i - f) p (volume.restrict Ω)) l (𝓝 0))
    (hlg : Tendsto (fun i => eLpNorm (gs i - g) r (volume.restrict Ω)) l (𝓝 0)) :
    HasWeakLineDeriv Ω v f g := by
  refine (hasWeakLineDeriv_iff_integral (locallyIntegrableOn_of_memLp hp hf)
    (locallyIntegrableOn_of_memLp hr hg)).2 fun φ => ?_
  have hfs := eventually_memLp_of_tendsto hf hlf
  have hgs := eventually_memLp_of_tendsto hg hlg
  refine tendsto_nhds_unique (tendsto_integral_testFunction_smul hr φ hgs hg hlg) ?_
  have hlim := (tendsto_integral_testFunction_smul hp (∂^{v} φ) hfs hf hlf).const_smul
    ((-1 : ℝ) ^ k)
  exact hlim.congr fun i => ((h i).integral_eq φ).symm

/-! ### The bridge to tempered distributions -/

section Bridge

variable {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]

/-- An `L_p(V)` function, `1 ≤ p`, is locally integrable on `V`: the case `Ω = V` of
`Rd.locallyIntegrableOn_of_memLp`. -/
theorem locallyIntegrableOn_top_Lp (f : Lp ℂ p (volume : Measure V)) :
    LocallyIntegrableOn f ((⊤ : Opens V) : Set V) volume :=
  locallyIntegrableOn_of_memLp Fact.out (by simpa using Lp.memLp f)

/-- **`W^1_p(V)` from first-order weak derivatives**: a function `f ∈ L_p(V)`, `1 ≤ p`, with a
weak derivative `∂_v f ∈ L_p(V)` in every direction `v` lies in `W^1_p(V)`
(`Rd.memSobolev_iff_exists_hasWeakLineDeriv`; the derivative of order zero is `f` itself). -/
theorem memSobolev_one_of_forall_hasWeakLineDeriv {f : Lp ℂ p (volume : Measure V)}
    (h : ∀ v : V, ∃ g : Lp ℂ p (volume : Measure V), HasWeakLineDeriv ⊤ (fun _ : Fin 1 => v) f g) :
    MemSobolev 1 f := by
  refine (memSobolev_iff_exists_hasWeakLineDeriv _).2 fun k hk v => ?_
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk with rfl | rfl
  · exact ⟨_, hasWeakLineDeriv_fin_zero v (locallyIntegrableOn_top_Lp _)⟩
  have hv : v = fun _ => v 0 := funext fun i => congrArg v (Subsingleton.elim i 0)
  rw [hv]
  exact h (v 0)

/-- On `Ω = V`, the distribution of `f ∈ L_p(V)` applied to a test function `φ` is the tempered
distribution of `f` applied to the Schwartz function `φ`: both are `∫ φ f`. -/
theorem ofFun_top_apply (f : Lp ℂ p (volume : Measure V)) (φ : 𝓓((⊤ : Opens V), ℝ)) :
    Distribution.ofFun ⊤ (f : V → ℂ) volume ⊤ φ = (f : 𝓢'(V, ℂ)) (testSchwartz φ) := by
  rw [Distribution.ofFun_apply (locallyIntegrableOn_top_Lp f), Lp.toTemperedDistribution_apply]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [Complex.real_smul]

/-- On `Ω = V`, the iterated derivatives of `f ∈ L_p(V)` as a distribution and as a tempered
distribution agree on test functions. -/
theorem iteratedLineDerivOp_ofFun_top_apply (v : Fin k → V) (f : Lp ℂ p (volume : Measure V))
    (φ : 𝓓((⊤ : Opens V), ℝ)) :
    ∂^{v} (Distribution.ofFun ⊤ (f : V → ℂ) volume ⊤) φ =
      ∂^{v} (f : 𝓢'(V, ℂ)) (testSchwartz φ) := by
  rw [Distribution.iteratedLineDerivOp_apply_apply, ofFun_top_apply,
    TemperedDistribution.iteratedLineDerivOp_apply_apply, map_smul,
    iteratedLineDerivOp_testSchwartz]
  simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_one]

/-- **Weak derivatives on `V` are derivatives of tempered distributions**: for `f ∈ L_p(V)` and
`g ∈ L_r(V)`, `1 ≤ p, r`, `g` is the weak derivative `∂^v f` on `V` iff `∂^v f = g` in
`𝓢'(V, ℂ)`. One direction tests with the Schwartz functions `Rd.testSchwartz φ`; the other uses
that tempered distributions are determined by test functions (`Rd.eq_zero_of_testSchwartz`). -/
theorem hasWeakLineDeriv_top_iff {f : Lp ℂ p (volume : Measure V)}
    {g : Lp ℂ r (volume : Measure V)} :
    HasWeakLineDeriv ⊤ v f g ↔ ∂^{v} (f : 𝓢'(V, ℂ)) = (g : 𝓢'(V, ℂ)) := by
  constructor
  · intro h
    rw [← sub_eq_zero]
    refine eq_zero_of_testSchwartz fun φ => ?_
    have h' := DFunLike.congr_fun h.eq φ
    rw [iteratedLineDerivOp_ofFun_top_apply, ofFun_top_apply] at h'
    simp [h']
  · intro h
    refine ⟨locallyIntegrableOn_top_Lp f, locallyIntegrableOn_top_Lp g, ?_⟩
    ext φ
    rw [iteratedLineDerivOp_ofFun_top_apply, ofFun_top_apply, h]

/-- The iterated derivative `∂^v` of the `L_p(V)` class of a Schwartz function `η`, as a tempered
distribution, is the `L_r(V)` class of the Schwartz function `∂^v η`, as a tempered
distribution. -/
theorem iteratedLineDerivOp_toLp_eq (η : 𝓢(V, ℂ)) (v : Fin k → V) :
    ∂^{v} ((η.toLp p (volume : Measure V) : Lp ℂ p (volume : Measure V)) : 𝓢'(V, ℂ)) =
      ((∂^{v} η).toLp r (volume : Measure V) : 𝓢'(V, ℂ)) := by
  rw [Lp.toTemperedDistribution_toLp_eq, Lp.toTemperedDistribution_toLp_eq,
    TemperedDistribution.iteratedLineDerivOp_toTemperedDistributionCLM_eq]

/-- **Schwartz functions**: on every open set `Ω`, the classical iterated derivative `∂^v η` of a
Schwartz function `η` is its weak derivative. -/
theorem hasWeakLineDeriv_schwartz (Ω : Opens V) (η : 𝓢(V, ℂ)) (v : Fin k → V) :
    HasWeakLineDeriv Ω v η ((∂^{v} η : 𝓢(V, ℂ)) : V → ℂ) := by
  have h := (hasWeakLineDeriv_top_iff (p := 2) (r := 2)).2
    (iteratedLineDerivOp_toLp_eq (p := 2) (r := 2) η v)
  refine (h.congr_ae ?_ ?_).mono le_top
  · rw [volume_restrict_top]
    exact η.coeFn_toLp 2 volume
  · rw [volume_restrict_top]
    exact (∂^{v} η).coeFn_toLp 2 volume

/-- **Sobolev spaces by tempered distributions**: `f ∈ L_p(V)` lies in `W^m_p(V)` iff for every
order `k ≤ m` and all directions `v`, the tempered derivative `∂^v f` is an `L_p(V)` function
(`Rd.memSobolev_iff_exists_hasWeakLineDeriv` and `Rd.hasWeakLineDeriv_top_iff`). -/
theorem memSobolev_iff_tempered {m : ℕ} (f : Lp ℂ p (volume : Measure V)) :
    MemSobolev m f ↔ ∀ k ≤ m, ∀ v : Fin k → V,
      ∃ g : Lp ℂ p (volume : Measure V), ∂^{v} (f : 𝓢'(V, ℂ)) = (g : 𝓢'(V, ℂ)) :=
  (memSobolev_iff_exists_hasWeakLineDeriv f).trans <| forall₂_congr fun _ _ =>
    forall_congr' fun _ => exists_congr fun _ => hasWeakLineDeriv_top_iff

/-- Schwartz functions lie in every Sobolev space `W^m_p(V)`. -/
theorem memSobolev_toLp (η : 𝓢(V, ℂ)) (m : ℕ) :
    MemSobolev m (η.toLp p (volume : Measure V)) :=
  (memSobolev_iff_tempered _).2 fun _ _ v => ⟨_, iteratedLineDerivOp_toLp_eq (r := p) η v⟩

end Bridge

end Rd
