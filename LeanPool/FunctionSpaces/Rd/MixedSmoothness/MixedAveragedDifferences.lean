/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.MixedSmoothness.MixedDifferences
public import LeanPool.FunctionSpaces.Rd.Differences.MomentKernels

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Averaged mixed differences

Convolutions with tensor products of dilated bumps average translates of `f`: for one-dimensional
kernels `κ_i = ∑_t q_i(t) g_{c_i/ν(t)}` with integers `ν(t) ≥ 1` and the steps
`Y_i = δ_{-z_i e_i / c_i}` of the algebra of translations,

`((⊗κ) ⋆ f)(x) = ∫ (⊗g)(z) (∏_i ∑_t q_i(t) Y_i^{ν(t)}) f(x) dz`

for almost every `x` (`Rd.conv_tensorKernel_sum_dilate_ae`): the product expands into translates
`f(x - (ν(n_i) z_i / c_i)_i)` (`Rd.diffAct_prod_sum_pow_apply`), and each of them integrates to a
convolution with an anisotropically dilated tensor product
(`Rd.integral_tensorKernel_mul_comp_eq_conv`).

The moment kernels of `FunctionSpaces.Rd.Differences.MomentKernels` are of this form with the
polynomial `P(Y) = ∑_{l=1}^L (-1)^(l+1) C(L, l) Y^l = 1 - (-1)^L (Y - 1)^L`
(`Rd.sum_jacksonCoeff_smul_pow`), so polynomials in the translations factor through differences.
Their action on `L_p` is bounded through a small calculus (`Rd.ActsBounded`): translations act with
norm `1`, and sums, products and powers add and multiply the bounds.
-/

@[expose] public section

open MeasureTheory Filter
open TranslationAlgebra (diffAct diffAct_single)
open scoped ENNReal

namespace Rd

variable {d : ℕ}

/-! ### Bounded action of the algebra of translations -/

/-- An element `a` of the algebra of translations **acts boundedly on `L_p`** with constant `C`:
`a` keeps a.e. strong measurability and `‖a G‖_p ≤ C ‖G‖_p`. -/
def ActsBounded (p : ℝ≥0∞) (a : AddMonoidAlgebra ℂ (Fin d → ℝ)) (C : ℝ≥0∞) : Prop :=
  ∀ G : (Fin d → ℝ) → ℂ, AEStronglyMeasurable G volume →
    AEStronglyMeasurable (diffAct a G) volume ∧
      eLpNorm (diffAct a G) p volume ≤ C * eLpNorm G p volume

namespace ActsBounded

variable {p : ℝ≥0∞} {a b : AddMonoidAlgebra ℂ (Fin d → ℝ)} {C D : ℝ≥0∞}

/-- The unit acts with norm `1`. -/
theorem one : ActsBounded p (1 : AddMonoidAlgebra ℂ (Fin d → ℝ)) 1 := fun G hG => by
  simp only [map_one, one_apply_eq_self, one_mul]
  exact ⟨hG, le_rfl⟩

/-- `c δ_v` acts with norm `|c|`: translations preserve `L_p` norms. -/
theorem single (v : Fin d → ℝ) (c : ℂ) :
    ActsBounded p (AddMonoidAlgebra.single v c) ‖c‖ₑ := fun G hG => by
  have h : diffAct (AddMonoidAlgebra.single v c) G = c • fun x => G (x + v) :=
    funext fun x => diffAct_single v c G x
  rw [h, eLpNorm_const_smul, eLpNorm_comp_add_right hG]
  exact ⟨(aestronglyMeasurable_comp_add hG v).const_smul c, le_rfl⟩

/-- Larger constants are bounds too. -/
theorem mono (ha : ActsBounded p a C) (hCD : C ≤ D) : ActsBounded p a D := fun G hG =>
  ⟨(ha G hG).1, (ha G hG).2.trans (mul_le_mul' hCD le_rfl)⟩

/-- Sums act with the sum of the bounds. -/
theorem add (hp : 1 ≤ p) (ha : ActsBounded p a C) (hb : ActsBounded p b D) :
    ActsBounded p (a + b) (C + D) := fun G hG => by
  obtain ⟨h1, h2⟩ := ha G hG
  obtain ⟨h3, h4⟩ := hb G hG
  rw [map_add, LinearMap.add_apply]
  refine ⟨h1.add h3, (eLpNorm_add_le hp).trans ?_⟩
  rw [add_mul]
  exact add_le_add h2 h4

/-- Products act with the product of the bounds. -/
theorem mul (ha : ActsBounded p a C) (hb : ActsBounded p b D) :
    ActsBounded p (a * b) (C * D) := fun G hG => by
  obtain ⟨h1, h2⟩ := hb G hG
  obtain ⟨h3, h4⟩ := ha _ h1
  rw [map_mul, mul_apply_eq_comp]
  refine ⟨h3, h4.trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul' le_rfl h2

/-- Scalar multiples act with the scaled bound. -/
theorem smul (ha : ActsBounded p a C) (c : ℂ) : ActsBounded p (c • a) (‖c‖ₑ * C) := fun G hG => by
  obtain ⟨h1, h2⟩ := ha G hG
  rw [map_smul, LinearMap.smul_apply, eLpNorm_const_smul, mul_assoc]
  exact ⟨h1.const_smul c, mul_le_mul' le_rfl h2⟩

/-- Negatives act with the same bound. -/
theorem neg (ha : ActsBounded p a C) : ActsBounded p (-a) C := by
  have h := ha.smul (-1)
  rwa [neg_one_smul, eNorm_neg, eNorm_one, one_mul] at h

/-- Differences act with the sum of the bounds. -/
theorem sub (hp : 1 ≤ p) (ha : ActsBounded p a C) (hb : ActsBounded p b D) :
    ActsBounded p (a - b) (C + D) := by
  rw [sub_eq_add_neg]
  exact ha.add hp hb.neg

/-- Powers act with the power of the bound. -/
theorem pow (ha : ActsBounded p a C) (n : ℕ) : ActsBounded p (a ^ n) (C ^ n) := by
  induction n with
  | zero => simpa using (one : ActsBounded p (1 : AddMonoidAlgebra ℂ (Fin d → ℝ)) 1)
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul ha

/-- Finite products act with the product of the bounds. -/
theorem prod {ι : Type*} (s : Finset ι) {a : ι → AddMonoidAlgebra ℂ (Fin d → ℝ)} {C : ι → ℝ≥0∞}
    (h : ∀ i ∈ s, ActsBounded p (a i) (C i)) :
    ActsBounded p (∏ i ∈ s, a i) (∏ i ∈ s, C i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (one : ActsBounded p (1 : AddMonoidAlgebra ℂ (Fin d → ℝ)) 1)
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end ActsBounded

/-! ### The moment kernel polynomial -/

/-- **The polynomial of the moment kernels**: in a commutative `ℂ`-algebra,
`∑_{l<L} (-1)^l C(L, l + 1) Y^(l+1) = 1 - (-1)^L (Y - 1)^L`, by the binomial theorem. -/
theorem sum_jacksonCoeff_smul_pow {A : Type*} [CommRing A] [Algebra ℂ A] (L : ℕ) (Y : A) :
    ∑ l ∈ Finset.range L, jacksonCoeff L l • Y ^ (l + 1) = 1 - (-1) ^ L * (Y - 1) ^ L := by
  have hsign : ∀ m ≤ L, (-1 : A) ^ L * (-1) ^ (L - m) = (-1) ^ m := fun m hm => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [Nat.add_sub_cancel_left, pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
      one_pow, mul_one]
  have hexp : (-1 : A) ^ L * (Y - 1) ^ L =
      ∑ m ∈ Finset.range (L + 1), (-1 : A) ^ m * (L.choose m : A) * Y ^ m := by
    rw [sub_eq_add_neg, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmL : m ≤ L := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    rw [← hsign m hmL]
    ring
  rw [hexp, Finset.sum_range_succ']
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, sub_add_cancel_right,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [jacksonCoeff, Algebra.smul_def, map_mul, map_pow, map_neg, map_one, map_natCast, pow_succ]
  ring

/-- The moment kernel polynomial `P(Y) = 1 - (-1)^L (Y - 1)^L` of a translation acts with norm at
most `1 + 2^L`. -/
theorem actsBounded_momentPoly {p : ℝ≥0∞} (hp : 1 ≤ p) (L : ℕ) (v : Fin d → ℝ) :
    ActsBounded p (1 - (-1) ^ L * (AddMonoidAlgebra.single v (1 : ℂ) - 1) ^ L) (1 + 2 ^ L) := by
  have hY : ActsBounded p (AddMonoidAlgebra.single v (1 : ℂ) - 1) 2 := by
    have h := (ActsBounded.single (p := p) v (1 : ℂ)).sub hp ActsBounded.one
    rwa [eNorm_one, one_add_one_eq_two] at h
  have hsign : ActsBounded p ((-1 : AddMonoidAlgebra ℂ (Fin d → ℝ)) ^ L) 1 := by
    have h := (ActsBounded.one (p := p) (d := d)).neg.pow L
    rwa [one_pow] at h
  have h := ActsBounded.one.sub hp (hsign.mul (hY.pow L))
  rwa [one_mul] at h

/-- The polynomial `(-1)^L ((Y + 1)^L - 1)` of a translation acts with norm at most `2^L + 1`. -/
theorem actsBounded_addPoly {p : ℝ≥0∞} (hp : 1 ≤ p) (L : ℕ) (v : Fin d → ℝ) :
    ActsBounded p ((-1) ^ L * ((AddMonoidAlgebra.single v (1 : ℂ) + 1) ^ L - 1)) (2 ^ L + 1) := by
  have hY : ActsBounded p (AddMonoidAlgebra.single v (1 : ℂ) + 1) 2 := by
    have h := (ActsBounded.single (p := p) v (1 : ℂ)).add hp ActsBounded.one
    rwa [eNorm_one, one_add_one_eq_two] at h
  have hsign : ActsBounded p ((-1 : AddMonoidAlgebra ℂ (Fin d → ℝ)) ^ L) 1 := by
    have h := (ActsBounded.one (p := p) (d := d)).neg.pow L
    rwa [one_pow] at h
  have h := hsign.mul ((hY.pow L).sub hp ActsBounded.one)
  rwa [one_mul] at h

/-! ### Expanding products of polynomials in translations -/

/-- **Expansion**: `(∏_i ∑_t q_i(t) Y_i^{ν(t)}) f(x) = ∑_n (∏_i q_i(n_i)) f(x + (ν(n_i) w_i)_i)` for
the translations `Y_i = δ_{w_i e_i}`. -/
theorem diffAct_prod_sum_pow_apply {τ : Type*} (T : Finset τ) (ν : τ → ℕ) (q : Fin d → τ → ℂ)
    (w : Fin d → ℝ) (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    diffAct (∏ i, ∑ t ∈ T,
        q i t • AddMonoidAlgebra.single (Pi.single i (w i)) (1 : ℂ) ^ ν t) f x =
      ∑ n ∈ Fintype.piFinset fun _ => T,
        (∏ i, q i (n i)) * f (x + fun i => (ν (n i) : ℝ) * w i) := by
  have hterm : ∀ i t, q i t • AddMonoidAlgebra.single (Pi.single i (w i)) (1 : ℂ) ^ ν t =
      AddMonoidAlgebra.single (Pi.single i ((ν t : ℝ) * w i) : Fin d → ℝ) (q i t) := fun i t => by
    rw [AddMonoidAlgebra.single_pow, one_pow, AddMonoidAlgebra.smul_single', mul_one]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  simp_rw [hterm]
  rw [Finset.prod_univ_sum]
  simp_rw [AddMonoidAlgebra.prod_single]
  rw [map_sum, LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [diffAct_single]
  congr 2
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

/-! ### Convolution with tensor products of dilated bumps -/

/-- Diagonal changes of variables keep integrability. -/
theorem integrable_comp_diag {a : Fin d → ℝ} (ha : ∀ i, 0 < a i) {F : (Fin d → ℝ) → ℂ}
    (hF : Integrable F) : Integrable (fun z : Fin d → ℝ => F fun i => a i * z i) := by
  have hdet : LinearMap.det (diagMap a) ≠ 0 := by
    rw [det_diagMap]
    exact Finset.prod_ne_zero_iff.2 fun i _ => (ha i).ne'
  have hmap := Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet
  have he := (diagEquiv fun i => (ha i).ne').measurableEmbedding
  have hcoe : ⇑(diagEquiv fun i => (ha i).ne') = ⇑(diagMap a) := by
    funext z
    rw [diagMap_apply, diagEquiv_apply]
  have h1 : Integrable F (Measure.map (diagEquiv fun i => (ha i).ne') volume) := by
    rw [hcoe, hmap]
    exact hF.smul_measure ENNReal.ofReal_ne_top
  have h2 := he.integrable_map_iff.1 h1
  simpa only [Function.comp_def, diagEquiv_apply] using h2

/-- **Convolution with tensor products of dilated bumps averages translates**: for
`κ_i = ∑_{t ∈ T} q_i(t) g_{c_i/ν(t)}` with `ν(t) ≥ 1`, `c_i > 0` and `f ∈ L_p`,
`((⊗κ) ⋆ f)(x) = ∫ (⊗g)(z) (∏_i ∑_t q_i(t) Y_i^{ν(t)}) f(x) dz` with `Y_i = δ_{-z_i e_i / c_i}`, for
almost every `x`. -/
theorem conv_tensorKernel_sum_dilate_ae {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ∞) {g : ℝ → ℂ}
    (hg : Integrable g) {τ : Type*} (T : Finset τ) (ν : τ → ℕ) (hν : ∀ t ∈ T, 1 ≤ ν t)
    (q : Fin d → τ → ℂ) {c : Fin d → ℝ} (hc : ∀ i, 0 < c i) {f : (Fin d → ℝ) → ℂ}
    (hf : MemLp f p volume) :
    conv (tensorKernel fun i => ∑ t ∈ T, q i t • dilate (c i / ν t) g) f volume =ᵐ[volume]
      fun x => ∫ z, tensorKernel (fun _ => g) z * diffAct (∏ i, ∑ t ∈ T,
        q i t • AddMonoidAlgebra.single (Pi.single i (-z i / c i)) (1 : ℂ) ^ ν t) f x := by
  set S := Fintype.piFinset fun _ : Fin d => T
  set K : (Fin d → τ) → (Fin d → ℝ) → ℂ := fun n =>
    tensorKernel fun i => dilate (c i / ν (n i)) g
  have hνpos : ∀ n ∈ S, ∀ i, (0 : ℝ) < ν (n i) := fun n hn i => by
    have := hν (n i) (Fintype.mem_piFinset.1 hn i)
    exact_mod_cast this
  have hK : ∀ n ∈ S, Integrable (K n) := fun n hn =>
    integrable_tensorKernel fun i => integrable_dilate hg
      (div_pos (hc i) (hνpos n hn i)).ne'
  -- the kernel as a sum of tensor products
  have hker : (tensorKernel fun i => ∑ t ∈ T, q i t • dilate (c i / ν t) g) =
      fun x => ∑ n ∈ S, (∏ i, q i (n i)) * K n x := by
    rw [← sum_tensorKernel_piFinset (fun _ => T) fun i t => q i t • dilate (c i / ν t) g]
    funext x
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [K, tensorKernel, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
  -- the convolutions exist almost everywhere
  have hex : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)), ∀ n ∈ S,
      ConvolutionExistsAt (K n) f x (ContinuousLinearMap.mul ℂ ℂ) volume :=
    (Filter.eventually_all_finset _).2 fun n hn => ae_convolutionExistsAt hp1 hp (hK n hn) hf
  rw [hker]
  filter_upwards [conv_finsetSum_kernel_ae hp1 hp S (fun n => ∏ i, q i (n i)) hK hf, hex]
    with x h1 h2
  rw [h1]
  -- each convolution is an integral of a translate
  have hsub : ∀ n ∈ S, conv (K n) f volume x =
      ∫ z, tensorKernel (fun _ => g) z * f (x - fun i => ν (n i) / c i * z i) := fun n hn => by
    rw [integral_tensorKernel_mul_comp_eq_conv (fun _ => g)
      (fun i => div_pos (hνpos n hn i) (hc i)) f x]
    simp only [K, inv_div]
  have hint : ∀ n ∈ S, Integrable (fun z : Fin d → ℝ =>
      tensorKernel (fun _ => g) z * f (x - fun i => (ν (n i) : ℝ) / c i * z i)) := fun n hn => by
    have ha : ∀ i, (0 : ℝ) < ν (n i) / c i := fun i => div_pos (hνpos n hn i) (hc i)
    have h := integrable_comp_diag ha (h2 n hn)
    have hprod : (0 : ℝ) < ∏ i, c i / ν (n i) :=
      Finset.prod_pos fun i _ => div_pos (hc i) (hνpos n hn i)
    have hKD : ∀ z : Fin d → ℝ, K n (fun i => (ν (n i) : ℝ) / c i * z i) =
        ((∏ i, c i / ν (n i) : ℝ) : ℂ) * tensorKernel (fun _ => g) z := fun z => by
      simp only [K, tensorKernel, dilate, Module.finrank_self, pow_one, smul_eq_mul]
      rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [show c i / (ν (n i) : ℝ) * ((ν (n i) : ℝ) / c i * z i) = z i by
        field_simp [(hc i).ne', (hνpos n hn i).ne']]
    refine (h.const_mul ((((∏ i, c i / ν (n i))⁻¹ : ℝ)) : ℂ)).congr
      (Eventually.of_forall fun z => ?_)
    simp only [ContinuousLinearMap.mul_apply']
    rw [hKD z, ← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hprod.ne',
      Complex.ofReal_one, one_mul]
  calc ∑ n ∈ S, (∏ i, q i (n i)) * conv (K n) f volume x
      = ∑ n ∈ S, ∫ z, (∏ i, q i (n i)) *
          (tensorKernel (fun _ => g) z * f (x - fun i => ν (n i) / c i * z i)) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [hsub n hn, integral_const_mul]
    _ = ∫ z, ∑ n ∈ S, (∏ i, q i (n i)) *
          (tensorKernel (fun _ => g) z * f (x - fun i => ν (n i) / c i * z i)) :=
        (integral_finsetSum _ fun n hn => (hint n hn).const_mul _).symm
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only
        rw [diffAct_prod_sum_pow_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        have hx : (x - fun i => (ν (n i) : ℝ) / c i * z i) =
            x + fun i => (ν (n i) : ℝ) * (-z i / c i) := by
          funext i
          simp only [Pi.sub_apply, Pi.add_apply]
          ring
        rw [hx]
        ring

end Rd
