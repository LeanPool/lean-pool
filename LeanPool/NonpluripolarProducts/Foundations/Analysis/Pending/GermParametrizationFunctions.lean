/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GermAlgebraicParametrization
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.GermParametrizationData

/-!
# From germ-level algebra to pointwise parametrization identities

Blueprint `lag:substitution-relations`, `lag:ideal-comparison`,
`lag:parametrization-sets` (algebraic identities) (Demailly, *Complex analytic and
differential geometry*, II.4.15--4.19).

If `A` is an analytic germ whose vanishing ideal is prime and carries
`AlgebraicParametrization (vanishingIdeal A) d`, then choosing holomorphic representatives
on a common small ball turns the germ identities into `ParametrizationData A`.  The two
substantive steps are substitution (`δ^s Q_k(x, B_k(x, t) / δ(x))` and
`δ^e R(x, B(x, t) / δ(x))` are multiples of `W(x, t)`, because they vanish at `u` modulo the
vanishing ideal) and completeness: a defining function `g` of `A` reduces to a polynomial
`R` in `z''` modulo the `Q_k(z', z_k)`, all of which vanish at the points
`(x, B(x, t) / δ(x))`.
-/

@[expose] public section

open Set Filter Metric Polynomial
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.GermParametrizationFunctions

open FirstPass RegularLocusDense AnalyticGermDecomposition GermAlgebraicParametrization
open GermParametrizationData

noncomputable section

section Germs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The underlying germ of a holomorphic germ. -/
abbrev toGerm : HolGerm E →+* Germ (𝓝 (0 : E)) ℂ := (holGermSubring E).subtype

theorem toGerm_mk (f : E → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) :
    toGerm (HolGerm.mk f hf) = (f : Germ (𝓝 (0 : E)) ℂ) :=
  rfl

theorem toGerm_injective : Function.Injective (toGerm : HolGerm E →+* _) :=
  Subtype.val_injective

/-- A chosen representative of a holomorphic germ. -/
def rep (g : HolGerm E) : E → ℂ := (HolGerm.exists_eq_mk g).choose

theorem eventually_differentiableAt_rep (g : HolGerm E) :
    ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (rep g) z :=
  (HolGerm.exists_eq_mk g).choose_spec.fst

theorem mk_rep (g : HolGerm E) : HolGerm.mk (rep g) (eventually_differentiableAt_rep g) = g :=
  (HolGerm.exists_eq_mk g).choose_spec.snd.symm

theorem toGerm_eq_rep (g : HolGerm E) : toGerm g = (rep g : Germ (𝓝 (0 : E)) ℂ) := by
  conv_lhs => rw [← mk_rep g]
  rfl

theorem rep_zero_eq (g : HolGerm E) : rep g 0 = HolGerm.eval g := by
  conv_rhs => rw [← mk_rep g]
  rfl

theorem germ_coe_sum {α R ι : Type*} [CommSemiring R] {l : Filter α} (s : Finset ι)
    (f : ι → α → R) :
    ((fun x => ∑ i ∈ s, f i x : α → R) : Germ l R) = ∑ i ∈ s, (f i : Germ l R) := by
  have h := map_sum (Germ.coeRingHom l : (α → R) →+* Germ l R) f s
  simp only [Germ.coe_coeRingHom] at h
  rw [← h, Finset.sum_fn]

theorem germ_coe_prod {α R ι : Type*} [CommSemiring R] {l : Filter α} (s : Finset ι)
    (f : ι → α → R) :
    ((fun x => ∏ i ∈ s, f i x : α → R) : Germ l R) = ∏ i ∈ s, (f i : Germ l R) := by
  have h := map_prod (Germ.coeRingHom l : (α → R) →+* Germ l R) f s
  simp only [Germ.coe_coeRingHom] at h
  rw [← h, Finset.prod_fn]

theorem germ_coe_add {α R : Type*} [Add R] {l : Filter α} (f g : α → R) :
    ((fun x => f x + g x : α → R) : Germ l R) = (f : Germ l R) + (g : Germ l R) :=
  rfl

/-- Constant polynomials, germwise. -/
def germC : Germ (𝓝 (0 : E)) ℂ →+* Germ (𝓝 (0 : E)) ℂ[X] where
  toFun g := g.map Polynomial.C
  map_one' := congrArg (fun f : E → ℂ[X] => (f : Germ (𝓝 (0 : E)) ℂ[X]))
    (funext fun _ => C_1)
  map_mul' a b := Germ.inductionOn₂ a b fun _ _ =>
    congrArg (fun f : E → ℂ[X] => (f : Germ (𝓝 (0 : E)) ℂ[X])) (funext fun _ => C_mul)
  map_zero' := congrArg (fun f : E → ℂ[X] => (f : Germ (𝓝 (0 : E)) ℂ[X]))
    (funext fun _ => C_0)
  map_add' a b := Germ.inductionOn₂ a b fun _ _ =>
    congrArg (fun f : E → ℂ[X] => (f : Germ (𝓝 (0 : E)) ℂ[X])) (funext fun _ => C_add)

omit [NormedSpace ℂ E] in
theorem germC_coe (f : E → ℂ) :
    germC (f : Germ (𝓝 (0 : E)) ℂ) = ((fun x => C (f x) : E → ℂ[X]) : Germ _ _) :=
  rfl

/-- A polynomial over holomorphic germs, as a germ of polynomial-valued functions. -/
def polyGerm : (HolGerm E)[X] →+* Germ (𝓝 (0 : E)) ℂ[X] :=
  eval₂RingHom (germC.comp toGerm) ((fun _ => X : E → ℂ[X]) : Germ _ _)

theorem polyGerm_C (c : HolGerm E) : polyGerm (C c) = germC (toGerm c) :=
  eval₂_C _ _

theorem polyGerm_X : polyGerm (X : (HolGerm E)[X]) = ((fun _ => X : E → ℂ[X]) : Germ _ _) :=
  eval₂_X _ _

theorem polyGerm_eq (F : (HolGerm E)[X]) {N : ℕ} (hN : F.natDegree < N) (a : ℕ → E → ℂ)
    (ha : ∀ j < N, toGerm (F.coeff j) = (a j : Germ (𝓝 (0 : E)) ℂ)) :
    polyGerm F = ((fun x => ∑ j ∈ Finset.range N, C (a j x) * X ^ j : E → ℂ[X]) :
      Germ _ _) := by
  conv_lhs => rw [F.as_sum_range_C_mul_X_pow' hN]
  rw [germ_coe_sum, map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [map_mul, map_pow, polyGerm_C, polyGerm_X, ha j (Finset.mem_range.1 hj)]
  rfl

theorem polyGerm_derivative (F : (HolGerm E)[X]) :
    polyGerm (derivative F) = (polyGerm F).map derivative := by
  induction F using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [derivative_add, map_add, hp, hq, map_add]
    induction polyGerm p using Germ.inductionOn with
    | h f =>
    induction polyGerm q using Germ.inductionOn with
    | h g =>
    exact congrArg (fun f : E → ℂ[X] => (f : Germ (𝓝 (0 : E)) ℂ[X]))
      (funext fun _ => (derivative_add).symm)
  | monomial j c =>
    rw [derivative_monomial, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow, polyGerm_C, polyGerm_X, map_natCast, toGerm_eq_rep]
    exact congrArg (fun f : E → ℂ[X] => (f : Germ (𝓝 (0 : E)) ℂ[X]))
      (funext fun x => by simp [derivative_X_pow, mul_assoc])

/-- If `W ∣ F` and both are represented pointwise, then pointwise `w x ∣ f x` near `0`. -/
theorem eventually_dvd {F W : (HolGerm E)[X]} (h : W ∣ F) {f w : E → ℂ[X]}
    (hf : polyGerm F = (f : Germ (𝓝 (0 : E)) ℂ[X])) (hw : polyGerm W = (w : Germ _ _)) :
    ∀ᶠ x in 𝓝 0, w x ∣ f x := by
  obtain ⟨G, rfl⟩ := h
  obtain ⟨g, hg⟩ : ∃ g : E → ℂ[X], polyGerm G = (g : Germ (𝓝 (0 : E)) ℂ[X]) :=
    Germ.inductionOn (p := fun φ => ∃ g : E → ℂ[X], φ = (g : Germ (𝓝 (0 : E)) ℂ[X]))
      (polyGerm G) fun g => ⟨g, rfl⟩
  rw [map_mul, hw, hg] at hf
  exact (Germ.coe_eq.1 hf).mono fun x hx => ⟨g x, hx.symm⟩

end Germs

section Polynomials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The coefficient functions `j ↦ rep (F.coeff j)` of a polynomial over germs, truncated
below `q`. -/
def coeffFun (F : (HolGerm E)[X]) (q j : ℕ) : E → ℂ :=
  if j < q then rep (F.coeff j) else 0

theorem toGerm_coeff_of_lt (F : (HolGerm E)[X]) {q j : ℕ} (hj : j < q) :
    toGerm (F.coeff j) = (coeffFun F q j : Germ (𝓝 (0 : E)) ℂ) := by
  rw [coeffFun, ite_eq_left hj, toGerm_eq_rep]

theorem eventually_differentiableAt_coeffFun (F : (HolGerm E)[X]) (q : ℕ) :
    ∀ᶠ x in 𝓝 (0 : E), ∀ j, DifferentiableAt ℂ (coeffFun F q j) x := by
  have h : ∀ᶠ x in 𝓝 (0 : E), ∀ j ∈ Finset.range q, DifferentiableAt ℂ (rep (F.coeff j)) x :=
    (eventually_all_finset _).2 fun j _ => eventually_differentiableAt_rep _
  refine h.mono fun x hx j => ?_
  unfold coeffFun
  split_ifs with hj
  · exact hx j (Finset.mem_range.2 hj)
  · exact differentiableAt_const (0 : ℂ)

theorem coeffFun_zero {F : (HolGerm E)[X]} {q : ℕ} (hF : ∀ j < q, HolGerm.eval (F.coeff j) = 0)
    (j : ℕ) : coeffFun F q j 0 = 0 := by
  unfold coeffFun
  split_ifs with hj
  · rw [rep_zero_eq, hF j hj]
  · rfl

/-- The pointwise monic polynomial `X ^ q + ∑_{j<q} C (a_j x) X ^ j`. -/
def monicPoly (q : ℕ) (a : ℕ → E → ℂ) (x : E) : ℂ[X] :=
  X ^ q + ∑ j ∈ Finset.range q, C (a j x) * X ^ j

/-- The pointwise polynomial `∑_{j<q} C (a_j x) X ^ j`. -/
def lowPoly (q : ℕ) (a : ℕ → E → ℂ) (x : E) : ℂ[X] :=
  ∑ j ∈ Finset.range q, C (a j x) * X ^ j

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
@[simp]
theorem eval_monicPoly (q : ℕ) (a : ℕ → E → ℂ) (x : E) (t : ℂ) :
    (monicPoly q a x).eval t = monicEval q a x t := by
  simp [monicPoly, monicEval, eval_finsetSum]

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
@[simp]
theorem eval_lowPoly (q : ℕ) (a : ℕ → E → ℂ) (x : E) (t : ℂ) :
    (lowPoly q a x).eval t = lowEval q a x t := by
  simp [lowPoly, lowEval, eval_finsetSum]

theorem polyGerm_monic {F : (HolGerm E)[X]} (hF : F.Monic) :
    polyGerm F = (monicPoly F.natDegree (coeffFun F F.natDegree) : Germ (𝓝 (0 : E)) ℂ[X]) := by
  rw [polyGerm_eq F (Nat.lt_succ_self _)
    (fun j => if j < F.natDegree then coeffFun F F.natDegree j else 1)]
  · refine congrArg (fun f : E → ℂ[X] => (f : Germ (𝓝 (0 : E)) ℂ[X])) (funext fun x => ?_)
    rw [Finset.sum_range_succ, ite_eq_right (lt_irrefl _), monicPoly, add_comm]
    simp only [Pi.one_apply, map_one, one_mul]
    exact congrArg _ (Finset.sum_congr rfl fun j hj => by rw [ite_eq_left (Finset.mem_range.1 hj)])
  · intro j hj
    rcases (Nat.lt_succ_iff.1 hj).lt_or_eq with hj | rfl
    · simp only [ite_eq_left hj]
      exact toGerm_coeff_of_lt F hj
    · simp only [lt_irrefl, ite_false]
      rw [hF.coeff_natDegree, map_one]
      rfl

theorem polyGerm_low (F : (HolGerm E)[X]) {q : ℕ} (hq : F.natDegree < q) :
    polyGerm F = (lowPoly q (coeffFun F q) : Germ (𝓝 (0 : E)) ℂ[X]) :=
  polyGerm_eq F hq _ fun _ hj => toGerm_coeff_of_lt F hj

theorem exists_polyGerm_eq (F : (HolGerm E)[X]) :
    ∃ f : E → ℂ[X], polyGerm F = (f : Germ (𝓝 (0 : E)) ℂ[X]) :=
  Germ.inductionOn (p := fun φ => ∃ f : E → ℂ[X], φ = (f : Germ (𝓝 (0 : E)) ℂ[X]))
    (polyGerm F) fun f => ⟨f, rfl⟩

end Polynomials

section Coordinates

variable {n d : ℕ}

theorem toGerm_projGerm (c : HolGerm (ComplexModel d)) :
    toGerm (HolGerm.projGerm n d c) = (toGerm c).compTendsto (coordinateProjection n d)
      (HolGerm.tendsto_clm_nhds_zero _) := by
  induction c using HolGerm.induction_on with
  | h f hf => rfl

theorem toGerm_coord (k : Fin n) :
    toGerm (coord k) = ((fun z : ComplexModel n => z k) : Germ (𝓝 (0 : ComplexModel n)) ℂ) :=
  rfl

theorem toGerm_evalGerm (F : (HolGerm (ComplexModel d))[X]) {N : ℕ} (hN : F.natDegree < N)
    (a : ℕ → ComplexModel d → ℂ)
    (ha : ∀ j < N, toGerm (F.coeff j) = (a j : Germ (𝓝 (0 : ComplexModel d)) ℂ))
    {g : HolGerm (ComplexModel n)} {h : ComplexModel n → ℂ}
    (hg : toGerm g = (h : Germ (𝓝 (0 : ComplexModel n)) ℂ)) :
    toGerm (evalGerm n F g) = ((fun z => ∑ j ∈ Finset.range N,
      a j (coordinateProjection n d z) * h z ^ j : ComplexModel n → ℂ) : Germ _ ℂ) := by
  rw [evalGerm, eval₂_eq_sum_range' _ hN, map_sum, germ_coe_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [map_mul, map_pow, toGerm_projGerm, ha j (Finset.mem_range.1 hj), hg]
  rfl

theorem toGerm_evalGerm_monic {F : (HolGerm (ComplexModel d))[X]} (hF : F.Monic)
    {g : HolGerm (ComplexModel n)} {h : ComplexModel n → ℂ}
    (hg : toGerm g = (h : Germ (𝓝 (0 : ComplexModel n)) ℂ)) :
    toGerm (evalGerm n F g) = ((fun z => monicEval F.natDegree (coeffFun F F.natDegree)
      (coordinateProjection n d z) (h z) : ComplexModel n → ℂ) : Germ _ ℂ) := by
  rw [toGerm_evalGerm F (Nat.lt_succ_self _)
    (fun j => if j < F.natDegree then coeffFun F F.natDegree j else 1) ?_ hg]
  · refine congrArg (fun f : ComplexModel n → ℂ => (f : Germ (𝓝 (0 : ComplexModel n)) ℂ))
      (funext fun z => ?_)
    rw [Finset.sum_range_succ, ite_eq_right (lt_irrefl _), monicEval, add_comm]
    simp only [Pi.one_apply, one_mul]
    exact congrArg _ (Finset.sum_congr rfl fun j hj => by rw [ite_eq_left (Finset.mem_range.1 hj)])
  · intro j hj
    rcases (Nat.lt_succ_iff.1 hj).lt_or_eq with hj | rfl
    · simp only [ite_eq_left hj]
      exact toGerm_coeff_of_lt F hj
    · simp only [lt_irrefl, ite_false]
      rw [hF.coeff_natDegree, map_one]
      rfl

theorem toGerm_evalGerm_low (F : (HolGerm (ComplexModel d))[X]) {q : ℕ} (hq : F.natDegree < q)
    {g : HolGerm (ComplexModel n)} {h : ComplexModel n → ℂ}
    (hg : toGerm g = (h : Germ (𝓝 (0 : ComplexModel n)) ℂ)) :
    toGerm (evalGerm n F g) = ((fun z => lowEval q (coeffFun F q)
      (coordinateProjection n d z) (h z) : ComplexModel n → ℂ) : Germ _ ℂ) :=
  toGerm_evalGerm F hq _ (fun _ hj => toGerm_coeff_of_lt F hj) hg

theorem toGerm_linearFormGerm (c : Fin n → ℂ) :
    toGerm (linearFormGerm n d c) =
      (fibreForm d (fun k _ => c k) : Germ (𝓝 (0 : ComplexModel n)) ℂ) := by
  rw [linearFormGerm, map_sum]
  change _ = ((fun z => ∑ k : Fin n, if d ≤ k.1 then c k * z k else 0 : ComplexModel n → ℂ) :
    Germ (𝓝 (0 : ComplexModel n)) ℂ)
  rw [germ_coe_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs
  · rfl
  · rfl

theorem toGerm_mvEval (R : MvPolynomial (Fin n) (HolGerm (ComplexModel d))) :
    toGerm (MvPolynomial.eval₂ (HolGerm.projGerm n d) coord R) =
      ((fun z => ∑ m ∈ R.support, rep (R.coeff m) (coordinateProjection n d z) *
        ∏ k, z k ^ m k : ComplexModel n → ℂ) : Germ (𝓝 (0 : ComplexModel n)) ℂ) := by
  rw [MvPolynomial.eval₂_eq', map_sum, germ_coe_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, map_prod, toGerm_projGerm, toGerm_eq_rep]
  change _ = ((fun z => rep (R.coeff m) (coordinateProjection n d z) : ComplexModel n → ℂ) :
    Germ (𝓝 (0 : ComplexModel n)) ℂ) * ((fun z => ∏ k, z k ^ m k : ComplexModel n → ℂ) : Germ _ ℂ)
  rw [germ_coe_prod]
  refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun k _ => ?_)
  rw [map_pow]
  rfl

end Coordinates

section Vanishing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem eventually_of_mem_vanishingIdeal {A : Set E} {φ : HolGerm E}
    (hφ : φ ∈ vanishingIdeal A) {f : E → ℂ} (hf : toGerm φ = (f : Germ (𝓝 (0 : E)) ℂ)) :
    ∀ᶠ z in 𝓝 0, z ∈ A → f z = 0 := by
  obtain ⟨g, hg, rfl, hgA⟩ := hφ
  exact ((Germ.coe_eq.1 hf).and hgA).mono fun z hz hzA => hz.1 ▸ hz.2 hzA

end Vanishing

section Algebra

variable {S : Type*} [CommRing S]

/-- `L ^ s + ∑_{i<s} c_i δ^{s-i} L^i = δ ^ s (z ^ s + ∑_{i<s} c_i z ^ i)` when `L = δ z`. -/
theorem pow_add_sum_subst (s : ℕ) (c : ℕ → S) {δ L z : S} (hL : L = δ * z) :
    L ^ s + ∑ i ∈ Finset.range s, c i * δ ^ (s - i) * L ^ i =
      δ ^ s * (z ^ s + ∑ i ∈ Finset.range s, c i * z ^ i) := by
  rw [hL, mul_add, Finset.mul_sum, mul_pow]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun i hi => ?_)
  rw [← pow_sub_mul_pow δ (Finset.mem_range.1 hi).le]
  ring

/-- The multivariate analogue of `pow_add_sum_subst`. -/
theorem sum_prod_subst {σ : Type*} [Fintype σ] (M : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → S)
    {δ : S} {L z : σ → S} {e : ℕ} (he : ∀ m ∈ M, ∑ k, m k ≤ e)
    (hL : ∀ m ∈ M, ∀ k, m k ≠ 0 → L k = δ * z k) :
    ∑ m ∈ M, c m * δ ^ (e - ∑ k, m k) * ∏ k, L k ^ m k =
      δ ^ e * ∑ m ∈ M, c m * ∏ k, z k ^ m k := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hprod : ∏ k, L k ^ m k = δ ^ (∑ k, m k) * ∏ k, z k ^ m k := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    by_cases hk : m k = 0
    · simp [hk]
    · rw [hL m hm k hk, mul_pow]
  rw [hprod, ← pow_sub_mul_pow δ (he m hm)]
  ring

end Algebra

section Parametrization

variable {n d : ℕ} {A : Set (ComplexModel n)} (P : AlgebraicParametrization (vanishingIdeal A) d)

/-- Coefficient functions of `W`. -/
abbrev wFun : ℕ → ComplexModel d → ℂ := coeffFun P.minpoly P.minpoly.natDegree

/-- Coefficient functions of `B_k`. -/
abbrev bFun (k : Fin n) : ℕ → ComplexModel d → ℂ := coeffFun (P.B k) P.minpoly.natDegree

/-- Coefficient functions of `Q_k`. -/
abbrev eFun (k : Fin n) : ℕ → ComplexModel d → ℂ :=
  coeffFun (P.coordPoly k) (P.coordPoly k).natDegree

/-- A representative of `δ`. -/
abbrev discFun : ComplexModel d → ℂ := rep P.disc

/-- The function `u = ∑_{k ≥ d} c_k z_k`. -/
abbrev uFun : ComplexModel n → ℂ := fibreForm d (fun k _ => P.coef k)

theorem polyGerm_minpoly :
    polyGerm P.minpoly = (monicPoly P.minpoly.natDegree (wFun P) :
      Germ (𝓝 (0 : ComplexModel d)) ℂ[X]) :=
  polyGerm_monic P.isWeierstrass_minpoly.1

theorem polyGerm_B (k : Fin n) :
    polyGerm (P.B k) = (lowPoly P.minpoly.natDegree (bFun P k) :
      Germ (𝓝 (0 : ComplexModel d)) ℂ[X]) :=
  polyGerm_low _ (P.natDegree_B_lt k)

theorem eventually_w_eq_zero :
    ∀ᶠ z in 𝓝 0, z ∈ A → monicEval P.minpoly.natDegree (wFun P)
      (coordinateProjection n d z) (uFun P z) = 0 :=
  eventually_of_mem_vanishingIdeal P.minpoly_mem
    (toGerm_evalGerm_monic P.isWeierstrass_minpoly.1 (toGerm_linearFormGerm _))

theorem eventually_disc_mul_eq :
    ∀ᶠ z in 𝓝 0, z ∈ A → ∀ k : Fin n, d ≤ k.1 →
      discFun P (coordinateProjection n d z) * z k =
        lowEval P.minpoly.natDegree (bFun P k) (coordinateProjection n d z) (uFun P z) := by
  have h : ∀ k : Fin n, ∀ᶠ z in 𝓝 0, d ≤ k.1 → z ∈ A →
      discFun P (coordinateProjection n d z) * z k =
        lowEval P.minpoly.natDegree (bFun P k) (coordinateProjection n d z) (uFun P z) := by
    intro k
    by_cases hk : d ≤ k.1
    · have := eventually_of_mem_vanishingIdeal (P.disc_mul_sub_mem k hk)
        (f := fun z => discFun P (coordinateProjection n d z) * z k -
          lowEval P.minpoly.natDegree (bFun P k) (coordinateProjection n d z) (uFun P z)) (by
          rw [map_sub, map_mul, toGerm_projGerm, toGerm_eq_rep, toGerm_coord,
            toGerm_evalGerm_low _ (P.natDegree_B_lt k) (toGerm_linearFormGerm _)]
          rfl)
      exact this.mono fun z hz _ hzA => sub_eq_zero.1 (hz hzA)
    · exact Eventually.of_forall fun _ h => absurd h hk
  exact (eventually_all.2 h).mono fun z hz hzA k hk => hz k hk hzA

theorem eventually_e_eq_zero :
    ∀ᶠ z in 𝓝 0, z ∈ A → ∀ k : Fin n, d ≤ k.1 →
      monicEval (P.coordPoly k).natDegree (eFun P k) (coordinateProjection n d z) (z k) = 0 := by
  have h : ∀ k : Fin n, ∀ᶠ z in 𝓝 0, d ≤ k.1 → z ∈ A →
      monicEval (P.coordPoly k).natDegree (eFun P k) (coordinateProjection n d z) (z k) = 0 := by
    intro k
    by_cases hk : d ≤ k.1
    · exact (eventually_of_mem_vanishingIdeal (P.coordPoly_mem k hk)
        (toGerm_evalGerm_monic (P.isWeierstrass_coordPoly k hk).1 (toGerm_coord k))).mono
          fun z hz _ hzA => hz hzA
    · exact Eventually.of_forall fun _ h => absurd h hk
  exact (eventually_all.2 h).mono fun z hz hzA k hk => hz k hk hzA

theorem eventually_recover :
    ∀ᶠ x in 𝓝 (0 : ComplexModel d), ∀ t : ℂ, monicEval P.minpoly.natDegree (wFun P) x t = 0 →
      ∑ k : Fin n, (if d ≤ k.1 then P.coef k * lowEval P.minpoly.natDegree (bFun P k) x t
        else 0) = discFun P x * t := by
  have h := eventually_dvd P.dvd_recover
    (f := fun x => (∑ k : Fin n, if d ≤ k.1 then C (P.coef k) *
      lowPoly P.minpoly.natDegree (bFun P k) x else 0) - C (discFun P x) * X) ?_
    (polyGerm_minpoly P)
  · refine h.mono fun x hx t ht => ?_
    have h0 := eval_eq_zero_of_dvd_of_eval_eq_zero hx (by rw [eval_monicPoly]; exact ht)
    rw [eval_sub, eval_finsetSum, sub_eq_zero] at h0
    simp only [eval_mul, eval_C, eval_X] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs
    · simp
    · simp
  · rw [map_sub, map_mul, polyGerm_C, polyGerm_X, toGerm_eq_rep, germC_coe, map_sum]
    change _ = ((fun x => ∑ k : Fin n, if d ≤ k.1 then C (P.coef k) *
      lowPoly P.minpoly.natDegree (bFun P k) x else 0 : ComplexModel d → ℂ[X]) :
        Germ (𝓝 (0 : ComplexModel d)) ℂ[X]) -
      ((fun x => C (discFun P x) : ComplexModel d → ℂ[X]) : Germ (𝓝 (0 : ComplexModel d)) ℂ[X]) *
      ((fun _ => X : ComplexModel d → ℂ[X]) : Germ (𝓝 (0 : ComplexModel d)) ℂ[X])
    rw [germ_coe_sum]
    refine congrArg₂ (· - ·) (Finset.sum_congr rfl fun k _ => ?_) rfl
    split_ifs
    · rw [map_mul, polyGerm_C, polyGerm_B]
      rfl
    · rw [map_zero]
      rfl

theorem eventually_simple :
    ∀ᶠ x in 𝓝 (0 : ComplexModel d), discFun P x ≠ 0 → ∀ t : ℂ,
      monicEval P.minpoly.natDegree (wFun P) x t = 0 →
        deriv (monicEval P.minpoly.natDegree (wFun P) x) t ≠ 0 := by
  obtain ⟨a, b, hab⟩ := P.bezout
  obtain ⟨fa, hfa⟩ := exists_polyGerm_eq a
  obtain ⟨fb, hfb⟩ := exists_polyGerm_eq b
  have h := congrArg polyGerm hab
  rw [map_add, map_mul, map_mul, polyGerm_derivative, hfa, hfb, polyGerm_minpoly, polyGerm_C,
    toGerm_eq_rep, germC_coe, Germ.map_coe] at h
  refine (Germ.coe_eq.1 h).mono fun x hx hδ t ht hd => hδ ?_
  have hfun : monicEval P.minpoly.natDegree (wFun P) x =
      fun t => (monicPoly P.minpoly.natDegree (wFun P) x).eval t :=
    funext fun t => (eval_monicPoly _ _ _ _).symm
  rw [hfun, Polynomial.deriv] at hd
  have := congrArg (eval t) hx
  simp only [Function.comp_apply, eval_add, eval_mul, eval_C, eval_monicPoly, ht, hd, mul_zero,
    add_zero] at this
  exact this.symm

/-- The polynomial `E_k(T) = B_k(T)^s + ∑_{i<s} q_i δ^{s-i} B_k(T)^i`, `s = deg Q_k`. -/
def substPoly (k : Fin n) : (HolGerm (ComplexModel d))[X] :=
  P.B k ^ (P.coordPoly k).natDegree + ∑ i ∈ Finset.range (P.coordPoly k).natDegree,
    C ((P.coordPoly k).coeff i * P.disc ^ ((P.coordPoly k).natDegree - i)) * P.B k ^ i

theorem quotient_mk_evalGerm_B {k : Fin n} (hk : d ≤ k.1) :
    Ideal.Quotient.mk (vanishingIdeal A) (evalGerm n (P.B k) (linearFormGerm n d P.coef)) =
      Ideal.Quotient.mk (vanishingIdeal A) (HolGerm.projGerm n d P.disc) *
        Ideal.Quotient.mk (vanishingIdeal A) (coord k) := by
  rw [← map_mul, Ideal.Quotient.eq, ← neg_sub, neg_mem_iff]
  exact P.disc_mul_sub_mem k hk

theorem evalGerm_substPoly_mem {k : Fin n} (hk : d ≤ k.1) :
    evalGerm n (substPoly P k) (linearFormGerm n d P.coef) ∈ vanishingIdeal A := by
  have hQ := P.coordPoly_mem k hk
  have hQ' : evalGerm n (P.coordPoly k) (coord k) = coord k ^ (P.coordPoly k).natDegree +
      ∑ i ∈ Finset.range (P.coordPoly k).natDegree,
        HolGerm.projGerm n d ((P.coordPoly k).coeff i) * coord k ^ i := by
    conv_lhs => rw [(P.isWeierstrass_coordPoly k hk).1.as_sum]
    simp [evalGerm, eval₂_finsetSum]
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hQ ⊢
  rw [hQ'] at hQ
  simp only [substPoly, evalGerm, eval₂_add, eval₂_pow, eval₂_finsetSum, eval₂_mul, eval₂_C,
    map_add, map_pow, map_sum, map_mul] at hQ ⊢
  rw [pow_add_sum_subst _ _ (quotient_mk_evalGerm_B P hk), hQ, mul_zero]

theorem polyGerm_substPoly {k : Fin n} :
    polyGerm (substPoly P k) = ((fun x => lowPoly P.minpoly.natDegree (bFun P k) x ^
      (P.coordPoly k).natDegree + ∑ i ∈ Finset.range (P.coordPoly k).natDegree,
        C (eFun P k i x * discFun P x ^ ((P.coordPoly k).natDegree - i)) *
          lowPoly P.minpoly.natDegree (bFun P k) x ^ i : ComplexModel d → ℂ[X]) :
      Germ (𝓝 (0 : ComplexModel d)) ℂ[X]) := by
  rw [substPoly, map_add, map_pow, map_sum, polyGerm_B]
  change _ = ((fun x => lowPoly P.minpoly.natDegree (bFun P k) x ^
      (P.coordPoly k).natDegree : ComplexModel d → ℂ[X]) : Germ (𝓝 (0 : ComplexModel d)) ℂ[X]) +
    ((fun x => ∑ i ∈ Finset.range (P.coordPoly k).natDegree,
        C (eFun P k i x * discFun P x ^ ((P.coordPoly k).natDegree - i)) *
          lowPoly P.minpoly.natDegree (bFun P k) x ^ i : ComplexModel d → ℂ[X]) :
      Germ (𝓝 (0 : ComplexModel d)) ℂ[X])
  rw [germ_coe_sum]
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun i hi => ?_)
  rw [map_mul, map_pow, polyGerm_C, polyGerm_B, map_mul, map_pow,
    toGerm_coeff_of_lt _ (Finset.mem_range.1 hi), toGerm_eq_rep]
  rfl

theorem eventually_subst :
    ∀ᶠ x in 𝓝 (0 : ComplexModel d), discFun P x ≠ 0 → ∀ t : ℂ,
      monicEval P.minpoly.natDegree (wFun P) x t = 0 → ∀ k : Fin n, d ≤ k.1 →
        monicEval (P.coordPoly k).natDegree (eFun P k) x
          (lowEval P.minpoly.natDegree (bFun P k) x t / discFun P x) = 0 := by
  have h : ∀ k : Fin n, ∀ᶠ x in 𝓝 (0 : ComplexModel d), d ≤ k.1 → discFun P x ≠ 0 →
      ∀ t : ℂ, monicEval P.minpoly.natDegree (wFun P) x t = 0 →
        monicEval (P.coordPoly k).natDegree (eFun P k) x
          (lowEval P.minpoly.natDegree (bFun P k) x t / discFun P x) = 0 := by
    intro k
    by_cases hk : d ≤ k.1
    · refine (eventually_dvd (P.dvd_of_mem _ (evalGerm_substPoly_mem P hk))
        (polyGerm_substPoly P) (polyGerm_minpoly P)).mono fun x hx _ hδ t ht => ?_
      have h0 := eval_eq_zero_of_dvd_of_eval_eq_zero hx (by rw [eval_monicPoly]; exact ht)
      simp only [eval_add, eval_pow, eval_finsetSum, eval_mul, eval_C, eval_lowPoly] at h0
      rw [pow_add_sum_subst _ _ (mul_div_cancel₀ _ hδ).symm] at h0
      exact (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hδ)
    · exact Eventually.of_forall fun _ h => absurd h hk
  exact (eventually_all.2 h).mono fun x hx hδ t ht k hk => hx k hk hδ t ht

end Parametrization

section Completeness

variable {n d : ℕ} {A : Set (ComplexModel n)} (P : AlgebraicParametrization (vanishingIdeal A) d)

/-- A bound `e` for the total degrees of the monomials of `R`. -/
def mvDeg (R : MvPolynomial (Fin n) (HolGerm (ComplexModel d))) : ℕ :=
  R.support.sup fun m => ∑ k, m k

theorem le_mvDeg (R : MvPolynomial (Fin n) (HolGerm (ComplexModel d))) :
    ∀ m ∈ R.support, ∑ k, m k ≤ mvDeg R :=
  fun _ hm => Finset.le_sup (f := fun m : Fin n →₀ ℕ => ∑ k, m k) hm

/-- `E_R(T) = ∑_m r_m δ^{e - |m|} ∏_k B_k(T)^{m_k}`, i.e. `δ^e R(z', B(T)/δ)`. -/
def mvSubstPoly (R : MvPolynomial (Fin n) (HolGerm (ComplexModel d))) :
    (HolGerm (ComplexModel d))[X] :=
  ∑ m ∈ R.support, C (R.coeff m * P.disc ^ (mvDeg R - ∑ k, m k)) * ∏ k, P.B k ^ m k

theorem evalGerm_mvSubstPoly_mem (R : MvPolynomial (Fin n) (HolGerm (ComplexModel d)))
    (hR : ∀ m ∈ R.support, ∀ i : Fin n, i.1 < d → m i = 0)
    (hmem : MvPolynomial.eval₂ (HolGerm.projGerm n d) coord R ∈ vanishingIdeal A) :
    evalGerm n (mvSubstPoly P R) (linearFormGerm n d P.coef) ∈ vanishingIdeal A := by
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hmem ⊢
  rw [MvPolynomial.eval₂_eq'] at hmem
  simp only [mvSubstPoly, evalGerm, eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_finsetProd,
    eval₂_pow, map_sum, map_mul, map_pow, map_prod] at hmem ⊢
  rw [sum_prod_subst (z := fun k => Ideal.Quotient.mk (vanishingIdeal A) (coord k)) _ _
    (le_mvDeg R) ?_, hmem, mul_zero]
  intro m hm k hk
  exact quotient_mk_evalGerm_B P (not_lt.1 fun h => hk (hR m hm k h))

theorem polyGerm_mvSubstPoly (R : MvPolynomial (Fin n) (HolGerm (ComplexModel d))) :
    polyGerm (mvSubstPoly P R) = ((fun x => ∑ m ∈ R.support,
      C (rep (R.coeff m) x * discFun P x ^ (mvDeg R - ∑ k, m k)) *
        ∏ k, lowPoly P.minpoly.natDegree (bFun P k) x ^ m k : ComplexModel d → ℂ[X]) :
      Germ (𝓝 (0 : ComplexModel d)) ℂ[X]) := by
  rw [mvSubstPoly, map_sum, germ_coe_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, map_prod, polyGerm_C, map_mul, map_pow, toGerm_eq_rep, toGerm_eq_rep]
  change _ = ((fun x => C (rep (R.coeff m) x * discFun P x ^ (mvDeg R - ∑ k, m k)) :
      ComplexModel d → ℂ[X]) : Germ (𝓝 (0 : ComplexModel d)) ℂ[X]) *
    ((fun x => ∏ k, lowPoly P.minpoly.natDegree (bFun P k) x ^ m k : ComplexModel d → ℂ[X]) :
      Germ (𝓝 (0 : ComplexModel d)) ℂ[X])
  rw [germ_coe_prod]
  refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun k _ => ?_)
  rw [map_pow, polyGerm_B]
  rfl

theorem eventually_mvSubst (R : MvPolynomial (Fin n) (HolGerm (ComplexModel d)))
    (hR : ∀ m ∈ R.support, ∀ i : Fin n, i.1 < d → m i = 0)
    (hmem : MvPolynomial.eval₂ (HolGerm.projGerm n d) coord R ∈ vanishingIdeal A) :
    ∀ᶠ x in 𝓝 (0 : ComplexModel d), ∀ t : ℂ, monicEval P.minpoly.natDegree (wFun P) x t = 0 →
      ∑ m ∈ R.support, rep (R.coeff m) x * discFun P x ^ (mvDeg R - ∑ k, m k) *
        ∏ k, lowEval P.minpoly.natDegree (bFun P k) x t ^ m k = 0 := by
  refine (eventually_dvd (P.dvd_of_mem _ (evalGerm_mvSubstPoly_mem P R hR hmem))
    (polyGerm_mvSubstPoly P R) (polyGerm_minpoly P)).mono fun x hx t ht => ?_
  have h0 := eval_eq_zero_of_dvd_of_eval_eq_zero hx (by rw [eval_monicPoly]; exact ht)
  simpa only [eval_finsetSum, eval_mul, eval_C, eval_prod, eval_pow, eval_lowPoly] using h0

theorem eventually_complete (hA : IsAnalyticGerm A) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), discFun P (coordinateProjection n d z) ≠ 0 →
      monicEval P.minpoly.natDegree (wFun P) (coordinateProjection n d z) (uFun P z) = 0 →
      (∀ k : Fin n, d ≤ k.1 → discFun P (coordinateProjection n d z) * z k =
        lowEval P.minpoly.natDegree (bFun P k) (coordinateProjection n d z) (uFun P z)) →
      z ∈ A := by
  obtain ⟨r, g, hg, hAg⟩ := hA
  have hgmem : ∀ j, HolGerm.mk (g j) (hg j) ∈ vanishingIdeal A := fun j =>
    mem_vanishingIdeal_mk.2 (hAg.mono fun z hz hzA => (hz.1 hzA) j)
  choose R q hR hReq using fun j => P.reduce (HolGerm.mk (g j) (hg j))
  have hRmem : ∀ j, MvPolynomial.eval₂ (HolGerm.projGerm n d) coord (R j) ∈
      vanishingIdeal A := by
    intro j
    rw [eq_sub_of_add_eq (hReq j).symm]
    refine sub_mem (hgmem j) (Ideal.sum_mem _ fun k _ => ?_)
    split_ifs with hk
    · exact Ideal.mul_mem_left _ _ (P.coordPoly_mem k hk)
    · exact zero_mem _
  have hfun : ∀ j, ∀ᶠ z in 𝓝 (0 : ComplexModel n), g j z =
      (∑ m ∈ (R j).support, rep ((R j).coeff m) (coordinateProjection n d z) *
        ∏ k, z k ^ m k) +
      ∑ k : Fin n, (if d ≤ k.1 then rep (q j k) z * monicEval (P.coordPoly k).natDegree
        (eFun P k) (coordinateProjection n d z) (z k) else 0) := by
    intro j
    refine Germ.coe_eq.1 ?_
    have h := congrArg toGerm (hReq j)
    rw [toGerm_mk, map_add, toGerm_mvEval, map_sum] at h
    rw [h, germ_coe_add]
    refine congrArg₂ (fun a b : Germ (𝓝 (0 : ComplexModel n)) ℂ => a + b) rfl ?_
    rw [germ_coe_sum (Finset.univ : Finset (Fin n))]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · rw [map_mul, toGerm_eq_rep,
        toGerm_evalGerm_monic (P.isWeierstrass_coordPoly k hk).1 (toGerm_coord k)]
      rfl
    · rw [map_zero]
      rfl
  have hproj := HolGerm.tendsto_clm_nhds_zero (coordinateProjection n d)
  have hmv : ∀ j, ∀ᶠ z in 𝓝 (0 : ComplexModel n), ∀ t : ℂ,
      monicEval P.minpoly.natDegree (wFun P) (coordinateProjection n d z) t = 0 →
      ∑ m ∈ (R j).support, rep ((R j).coeff m) (coordinateProjection n d z) *
        discFun P (coordinateProjection n d z) ^ (mvDeg (R j) - ∑ k, m k) *
        ∏ k, lowEval P.minpoly.natDegree (bFun P k) (coordinateProjection n d z) t ^ m k = 0 :=
    fun j => hproj.eventually (eventually_mvSubst P (R j) (hR j) (hRmem j))
  filter_upwards [hAg, eventually_all.2 hfun, eventually_all.2 hmv,
    hproj.eventually (eventually_subst P)] with z hzA hzg hzR hzs hδ hW hB
  refine hzA.2 fun j => ?_
  have hQ : ∀ k : Fin n, d ≤ k.1 → monicEval (P.coordPoly k).natDegree (eFun P k)
      (coordinateProjection n d z) (z k) = 0 := fun k hk => by
    rw [eq_div_of_mul_eq hδ ((mul_comm _ _).trans (hB k hk))]
    exact hzs hδ _ hW k hk
  have hRz : ∑ m ∈ (R j).support, rep ((R j).coeff m) (coordinateProjection n d z) *
      ∏ k, z k ^ m k = 0 := by
    have h0 := hzR j _ hW
    rw [sum_prod_subst (z := fun k => z k) _ _ (le_mvDeg (R j)) ?_] at h0
    · exact (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hδ)
    · intro m hm k hk
      exact (hB k (not_lt.1 fun h => hk (hR j m hm k h))).symm
  rw [hzg j, hRz, zero_add]
  refine Finset.sum_eq_zero fun k _ => ?_
  split_ifs with hk
  · rw [hQ k hk, mul_zero]
  · rfl

end Completeness

section Germ

variable {n d : ℕ} {A : Set (ComplexModel n)}

theorem prime_of_isPrime [(vanishingIdeal A).IsPrime] (f g : ComplexModel n → ℂ)
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) (hg : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ g z)
    (hfg : ∀ᶠ z in 𝓝 0, z ∈ A → f z * g z = 0) :
    (∀ᶠ z in 𝓝 0, z ∈ A → f z = 0) ∨ ∀ᶠ z in 𝓝 0, z ∈ A → g z = 0 := by
  have h : HolGerm.mk f hf * HolGerm.mk g hg ∈ vanishingIdeal A := by
    rw [← HolGerm.mk_mul]
    exact mem_vanishingIdeal_mk.2 hfg
  exact (Ideal.IsPrime.mem_or_mem ‹_› h).imp mem_vanishingIdeal_mk.1 mem_vanishingIdeal_mk.1

theorem base_of (P : AlgebraicParametrization (vanishingIdeal A) d) (h : ComplexModel d → ℂ)
    (hh : ∀ᶠ x in 𝓝 0, DifferentiableAt ℂ h x)
    (hA : ∀ᶠ z in 𝓝 0, z ∈ A → h (coordinateProjection n d z) = 0) :
    ∀ᶠ x in 𝓝 0, h x = 0 := by
  have := P.eq_zero_of_mem (HolGerm.mk h hh)
    (by rw [HolGerm.projGerm_mk]; exact mem_vanishingIdeal_mk.2 hA)
  rw [← HolGerm.mk_zero, HolGerm.mk_eq_mk_iff] at this
  exact this

theorem exists_eqn_of_not_le (P : AlgebraicParametrization (vanishingIdeal A) d)
    (B : Set (ComplexModel n)) (hB : IsAnalyticGerm B)
    (hAB : ¬ A ≤ᶠ[𝓝 0] B) :
    ∃ h : ComplexModel d → ℂ, (∀ᶠ x in 𝓝 0, DifferentiableAt ℂ h x) ∧
      ¬ (∀ᶠ x in 𝓝 0, h x = 0) ∧
        ∀ᶠ z in 𝓝 0, z ∈ A → z ∈ B → h (coordinateProjection n d z) = 0 := by
  obtain ⟨r, b, hb, hBb⟩ := hB
  obtain ⟨j, hj⟩ : ∃ j, HolGerm.mk (b j) (hb j) ∉ vanishingIdeal A := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    refine hAB ?_
    have := eventually_all.2 fun j => mem_vanishingIdeal_mk.1 (hcon j)
    exact (this.and hBb).mono fun z hz hzA => hz.2.2 fun j => hz.1 j hzA
  obtain ⟨c, hc0, G, hG⟩ := P.exists_eqn _ hj
  obtain ⟨gG, hgG, rfl⟩ := HolGerm.exists_eq_mk G
  refine ⟨rep c, eventually_differentiableAt_rep c, fun h0 => hc0 ?_, ?_⟩
  · rw [← mk_rep c, ← HolGerm.mk_zero, HolGerm.mk_eq_mk_iff]
    exact h0
  · have := eventually_of_mem_vanishingIdeal hG
      (f := fun z => rep c (coordinateProjection n d z) - b j z * gG z)
      (by rw [map_sub, map_mul, toGerm_projGerm, toGerm_eq_rep]; rfl)
    filter_upwards [this, hBb] with z hz hzB hzA hzB'
    have h1 := hz hzA
    rw [(hzB.1 hzB') j, zero_mul, sub_zero] at h1
    exact h1

end Germ

end

end SGPT.Foundations.Analysis.Pending.GermParametrizationFunctions

namespace SGPT.Foundations.Analysis.Pending.GermParametrizationData

open FirstPass RegularLocusDense AnalyticGermDecomposition GermAlgebraicParametrization
open GermParametrizationFunctions

variable {n : ℕ} {A : Set (ComplexModel n)}

theorem nonempty_parametrizationData (hA : IsAnalyticGerm A) [(vanishingIdeal A).IsPrime]
    {d : ℕ} (P : AlgebraicParametrization (vanishingIdeal A) d) :
    Nonempty (ParametrizationData A) := by
  have hd := (eventually_differentiableAt_coeffFun P.minpoly P.minpoly.natDegree).and <|
    (eventually_all.2 fun k => eventually_differentiableAt_coeffFun (P.B k)
      P.minpoly.natDegree).and <|
    (eventually_all.2 fun k => eventually_differentiableAt_coeffFun (P.coordPoly k)
      (P.coordPoly k).natDegree).and <|
    (eventually_differentiableAt_rep P.disc).and <|
    (eventually_recover P).and <| (eventually_subst P).and (eventually_simple P)
  have hn := (eventually_w_eq_zero P).and <| (eventually_disc_mul_eq P).and <|
    (eventually_e_eq_zero P).and (eventually_complete P hA)
  obtain ⟨r₁, hr₁, H₁⟩ := Metric.eventually_nhds_iff_ball.1 hd
  obtain ⟨r₂, hr₂, H₂⟩ := Metric.eventually_nhds_iff_ball.1 hn
  have h₁ : ∀ x ∈ ball (0 : ComplexModel d) (min r₁ r₂), _ := fun x hx =>
    H₁ x (ball_subset_ball (min_le_left _ _) hx)
  have h₂ : ∀ z ∈ ball (0 : ComplexModel n) (min r₁ r₂), _ := fun z hz =>
    H₂ z (ball_subset_ball (min_le_right _ _) hz)
  exact ⟨{
    dim := d
    dim_le := P.le
    deg := P.minpoly.natDegree
    deg_pos := P.natDegree_minpoly_pos
    rad := min r₁ r₂
    rad_pos := lt_min hr₁ hr₂
    w := wFun P
    differentiableOn_w := fun j x hx => ((h₁ x hx).1 j).differentiableWithinAt
    w_zero := fun j _ => coeffFun_zero P.isWeierstrass_minpoly.2 j
    disc := discFun P
    differentiableOn_disc := fun x hx => (h₁ x hx).2.2.2.1.differentiableWithinAt
    disc_not_eventually_zero := fun h => P.disc_ne_zero (by
      rw [← mk_rep P.disc, ← HolGerm.mk_zero, HolGerm.mk_eq_mk_iff]
      exact h)
    coef := fun k _ => P.coef k
    differentiableOn_coef := fun k => differentiableOn_const _
    b := bFun P
    differentiableOn_b := fun k j x hx => ((h₁ x hx).2.1 k j).differentiableWithinAt
    s := fun k => (P.coordPoly k).natDegree
    e := fun k => if d ≤ k.1 then eFun P k else fun _ _ => 0
    differentiableOn_e := fun k j x hx => by
      split_ifs
      · exact ((h₁ x hx).2.2.1 k j).differentiableWithinAt
      · exact differentiableWithinAt_const _
    e_zero := fun k j hj => by
      split_ifs with hk
      · exact coeffFun_zero (P.isWeierstrass_coordPoly k hk).2 j
      · rfl
    w_eq_zero := fun z hzA hz => (h₂ z hz).1 hzA
    disc_mul_eq := fun z hzA hz => (h₂ z hz).2.1 hzA
    e_eq_zero := fun z hzA hz k hk => by
      dsimp only
      rw [ite_eq_left hk]
      exact (h₂ z hz).2.2.1 hzA k hk
    recover := fun x hx => (h₁ x hx).2.2.2.2.1
    subst := fun x hx hδ t ht k hk => by
      rw [ite_eq_left hk]
      exact (h₁ x hx).2.2.2.2.2.1 hδ t ht k hk
    simple := fun x hx => (h₁ x hx).2.2.2.2.2.2
    complete := fun z hz => (h₂ z hz).2.2.2
    prime := prime_of_isPrime
    base := base_of P
    exists_eqn_of_not_le := exists_eqn_of_not_le P }⟩

end SGPT.Foundations.Analysis.Pending.GermParametrizationData
