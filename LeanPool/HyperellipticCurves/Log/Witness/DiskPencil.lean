/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Cantor.CantorPipeline

import LeanPool.HyperellipticCurves.ForMathlib.Polynomial
import LeanPool.HyperellipticCurves.Log.Ftau.GoodPosition

/-!
# The pencil of square roots through a disk centre (`lem:global-generic`, per-disk half)

The per-disk configuration `[P₀ + ι Q] + τ + [Q + ι P₀]` of `lem:global-generic` composes
the pair block of the disk centre `P₀ = (a, b)` and an auxiliary point `Q` with the datum
`τ`. Its stage-1 composed square root is the interpolant `V` with `V ≡ v_τ (mod u_τ)`,
`V(a) = b` and `V(x_Q) = -y_Q`, i.e. the curve `y = V(x)` through `supp τ`, `P₀` and `ι Q`.

Dropping the condition at `Q`, these interpolants form a **pencil**: they are exactly the
`ChabautyColeman.pencilV` at the parameters `t`, an affine line through
`ChabautyColeman.pencilV₀` with direction the modulus
`ChabautyColeman.pencilU = u_τ · (X - a)`. The residual cofactor
`ChabautyColeman.pencilW` is then *quadratic* in `t`
(`ChabautyColeman.pencilW_spec`), and `Q` is recovered from `t` as any root of it.

This turns each genericity condition of the per-disk configuration into a condition on the
single scalar `t`, each excluding only finitely many parameters:

* the stage-1 degree condition is `t ≠ 0` (`ChabautyColeman.natDegree_pencilV`);
* the conditions at a point `x` are conditions on the residual there, which is a nonzero
  quadratic in `t` (`ChabautyColeman.finite_setOf_eval_pencilW_eq_zero`) — degenerating to
  an affine condition on the base locus, where the modulus vanishes;
* the member must meet the curve transversally away from the base locus. This is the only
  condition not visibly affine, and it is finite for a reason with no hypotheses attached
  (`ChabautyColeman.finite_setOf_pencil_multiple_root`): a tangency at `x` puts the point
  `(x, V_t(x))` of the curve on the line `A·y + B = 0`
  (`ChabautyColeman.eval_pencilTang_eq_zero`), hence `x` among the roots of `A² f - B²`,
  which is nonzero because `B` has leading coefficient `1` in degree `3g+1`
  (`ChabautyColeman.coeff_pencilTangB`) while `A² f` and `B²` have degrees of opposite
  parity.

The good parameter is `ChabautyColeman.exists_pencil_param`, at any **nonsingular centre** —
`b ≠ 0`, or `a` a simple root of `f`. Transversality at the centre is a nonzero condition on
the parameter in both cases (`ChabautyColeman.pencilPar_ne_zero_of_nonsingular`); at a
Weierstrass centre it is even free for *every* member
(`ChabautyColeman.eval_pencilW₀_ne_zero_of_deriv` — differentiating the pencil identity
gives `W₀(a) = -f'(a)/u_τ(a)`). The curve-avoidance clause is restricted to the roots of `f`
other than `a`, which for `b ≠ 0` is the full clause: no root of `f` lies at `a`.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

section Pencil

variable {K : Type*} [Field K] {f uτ vτ : K[X]} {a b t x : K}

/-- The `u`-part of the base divisor of the pencil: that of `τ` times that of the disk
centre. It is the modulus of the interpolation problem defining the pencil. -/
noncomputable def pencilU (uτ : K[X]) (a : K) : K[X] := uτ * (X - C a)

/-- The base member of the pencil: the square root of `f` modulo `u_τ` taking the value
`b` at `a`, of degree at most `deg u_τ`. -/
noncomputable def pencilV₀ (uτ vτ : K[X]) (a b : K) : K[X] :=
  vτ + C ((b - vτ.eval a) / uτ.eval a) * uτ

/-- The residual cofactor of the base member of the pencil. -/
noncomputable def pencilW₀ (f uτ vτ : K[X]) (a b : K) : K[X] :=
  cantorCofactor f (pencilU uτ a) (pencilV₀ uτ vτ a b)

/-- The member of the pencil at parameter `t`. -/
noncomputable def pencilV (uτ vτ : K[X]) (a b t : K) : K[X] :=
  pencilV₀ uτ vτ a b + C t * pencilU uτ a

/-- The residual cofactor at parameter `t`. -/
noncomputable def pencilW (f uτ vτ : K[X]) (a b t : K) : K[X] :=
  C t ^ 2 * pencilU uτ a + 2 * C t * pencilV₀ uτ vτ a b + pencilW₀ f uτ vτ a b

theorem eval_pencilU : (pencilU uτ a).eval x = uτ.eval x * (x - a) := by simp [pencilU]

@[simp] theorem eval_pencilV :
    (pencilV uτ vτ a b t).eval x = (pencilV₀ uτ vτ a b).eval x + t * (pencilU uτ a).eval x := by
  simp [pencilV]

@[simp] theorem eval_pencilW :
    (pencilW f uτ vτ a b t).eval x = t ^ 2 * (pencilU uτ a).eval x
      + 2 * t * (pencilV₀ uτ vτ a b).eval x + (pencilW₀ f uτ vτ a b).eval x := by
  simp [pencilW]

@[simp] theorem derivative_pencilV : (pencilV uτ vτ a b t).derivative
    = (pencilV₀ uτ vτ a b).derivative + C t * (pencilU uτ a).derivative := by
  simp [pencilV]

theorem pencilU_monic (hu : uτ.Monic) : (pencilU uτ a).Monic := hu.mul (monic_X_sub_C a)

theorem natDegree_pencilU (hu : uτ.Monic) :
    (pencilU uτ a).natDegree = uτ.natDegree + 1 := by
  rw [pencilU, hu.natDegree_mul (monic_X_sub_C a), natDegree_X_sub_C]

theorem dvd_pencilV₀_sub : uτ ∣ pencilV₀ uτ vτ a b - vτ :=
  ⟨C ((b - vτ.eval a) / uτ.eval a), by rw [pencilV₀]; ring⟩

theorem eval_pencilV₀ (h : uτ.eval a ≠ 0) : (pencilV₀ uτ vτ a b).eval a = b := by
  simp only [pencilV₀, eval_add, eval_mul, eval_C]
  field

/-- The pencil member is congruent to `v_τ` modulo `u_τ`. -/
theorem dvd_pencilV_sub : uτ ∣ pencilV uτ vτ a b t - vτ := by
  obtain ⟨c, hc⟩ := dvd_pencilV₀_sub (uτ := uτ) (vτ := vτ) (a := a) (b := b)
  exact ⟨c + C t * (X - C a), by rw [pencilV, pencilU]; linear_combination hc⟩

/-- Every member of the pencil passes through the disk centre. -/
theorem eval_pencilV_base (h : uτ.eval a ≠ 0) : (pencilV uτ vτ a b t).eval a = b := by
  rw [eval_pencilV, eval_pencilU, eval_pencilV₀ h, sub_self, mul_zero, mul_zero, add_zero]

theorem natDegree_pencilV₀_le (hv : vτ.degree < uτ.degree) :
    (pencilV₀ uτ vτ a b).natDegree ≤ uτ.natDegree :=
  (natDegree_add_le _ _).trans (max_le (natDegree_le_natDegree hv.le)
    (natDegree_C_mul_le _ _))

/-- The base member of the pencil is a square root of `f` modulo the modulus. -/
theorem pencilU_dvd_pencilV₀_sq_sub (hne : uτ.eval a ≠ 0) (hd : uτ ∣ vτ ^ 2 - f)
    (hb : b ^ 2 = f.eval a) : pencilU uτ a ∣ pencilV₀ uτ vτ a b ^ 2 - f := by
  obtain ⟨c, hc⟩ := dvd_pencilV₀_sub (uτ := uτ) (vτ := vτ) (a := a) (b := b)
  obtain ⟨w, hw⟩ := hd
  refine (isCoprime_X_sub_C_of_eval_ne_zero hne).mul_dvd
    ⟨w + 2 * vτ * c + uτ * c ^ 2, ?_⟩ ?_
  · linear_combination hw + (pencilV₀ uτ vτ a b + vτ + uτ * c) * hc
  · rw [dvd_iff_isRoot]
    simp [IsRoot, eval_pencilV₀ hne, hb]

theorem pencilW₀_spec (hu : uτ.Monic) (hne : uτ.eval a ≠ 0) (hd : uτ ∣ vτ ^ 2 - f)
    (hb : b ^ 2 = f.eval a) :
    pencilV₀ uτ vτ a b ^ 2 - f = pencilU uτ a * pencilW₀ f uτ vτ a b :=
  cantorCofactor_spec f (pencilU_monic hu) (pencilU_dvd_pencilV₀_sq_sub hne hd hb)

/-- **The pencil identity**: every member of the pencil is a square root of `f` modulo the
modulus, with the residual cofactor quadratic in the parameter. -/
theorem pencilW_spec (hu : uτ.Monic) (hne : uτ.eval a ≠ 0) (hd : uτ ∣ vτ ^ 2 - f)
    (hb : b ^ 2 = f.eval a) :
    pencilV uτ vτ a b t ^ 2 - f = pencilU uτ a * pencilW f uτ vτ a b t := by
  rw [pencilV, pencilW]
  linear_combination pencilW₀_spec hu hne hd hb

/-- **The stage-1 degree condition**: a member of the pencil has top degree exactly when
its parameter is nonzero — the degenerate member is the base member. -/
theorem natDegree_pencilV (ht : t ≠ 0) (hu : uτ.Monic) (hv : vτ.degree < uτ.degree) :
    (pencilV uτ vτ a b t).natDegree = uτ.natDegree + 1 := by
  have h : (C t * pencilU uτ a).natDegree = uτ.natDegree + 1 := by
    rw [natDegree_C_mul ht, natDegree_pencilU hu]
  have hlt : (pencilV₀ uτ vτ a b).natDegree < (C t * pencilU uτ a).natDegree := by
    lia [natDegree_pencilV₀_le (a := a) (b := b) hv]
  rw [pencilV, natDegree_add_eq_right_of_natDegree_lt hlt, h]

/-- The residual of the base member has the complementary degree; for `deg f = 2g+1` and
`deg u_τ = g` it is again `g`. -/
theorem natDegree_pencilW₀ (hu : uτ.Monic) (hne : uτ.eval a ≠ 0) (hd : uτ ∣ vτ ^ 2 - f)
    (hb : b ^ 2 = f.eval a) (hv : vτ.degree < uτ.degree)
    (hlt : 2 * uτ.natDegree < f.natDegree) :
    (pencilW₀ f uτ vτ a b).natDegree + (uτ.natDegree + 1) = f.natDegree := by
  have hV₀ := natDegree_pencilV₀_le (a := a) (b := b) hv
  have hpow := natDegree_pow_le (p := pencilV₀ uτ vτ a b) (n := 2)
  have hsq : (pencilV₀ uτ vτ a b ^ 2).natDegree < f.natDegree := by lia
  have hspec := pencilW₀_spec (b := b) hu hne hd hb
  have hne0 : pencilW₀ f uτ vτ a b ≠ 0 := fun h0 ↦ by
    rw [h0, mul_zero, sub_eq_zero] at hspec
    rw [hspec] at hsq
    exact lt_irrefl _ hsq
  have h := congrArg natDegree hspec
  rw [natDegree_sub_eq_right_of_natDegree_lt hsq,
    (pencilU_monic hu).natDegree_mul' hne0, natDegree_pencilU hu] at h
  lia

/-! ### Finiteness of the bad parameters -/

/-- The residual of the pencil at `x`, read as a polynomial in the pencil parameter. -/
noncomputable def pencilPar (f uτ vτ : K[X]) (a b x : K) : K[X] :=
  C ((pencilU uτ a).eval x) * X ^ 2 + C (2 * (pencilV₀ uτ vτ a b).eval x) * X
    + C ((pencilW₀ f uτ vτ a b).eval x)

@[simp] theorem eval_pencilPar :
    (pencilPar f uτ vτ a b x).eval t = (pencilW f uτ vτ a b t).eval x := by
  simp only [pencilPar, eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_pencilW]
  ring

theorem coeff_pencilPar_two :
    (pencilPar f uτ vτ a b x).coeff 2 = (pencilU uτ a).eval x := by
  simp only [pencilPar, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

theorem coeff_pencilPar_one :
    (pencilPar f uτ vτ a b x).coeff 1 = 2 * (pencilV₀ uτ vτ a b).eval x := by
  simp only [pencilPar, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

theorem pencilPar_ne_zero_of_pencilU (hx : (pencilU uτ a).eval x ≠ 0) :
    pencilPar f uτ vτ a b x ≠ 0 :=
  fun h0 ↦ hx (by rw [← coeff_pencilPar_two (f := f) (vτ := vτ) (b := b), h0, coeff_zero])

/-- On the base locus, where the modulus vanishes, the residual is still affine in the
parameter with nonzero leading coefficient. -/
theorem pencilPar_ne_zero_of_pencilV₀ [NeZero (2 : K)] (hx : (pencilV₀ uτ vτ a b).eval x ≠ 0) :
    pencilPar f uτ vτ a b x ≠ 0 := fun h0 ↦ by
  have := coeff_pencilPar_one (f := f) (uτ := uτ) (vτ := vτ) (a := a) (b := b) (x := x)
  rw [h0, coeff_zero] at this
  exact hx ((mul_eq_zero.mp this.symm).resolve_left (NeZero.ne (2 : K)))

/-- **Transversality is free at a Weierstrass centre**: for `a` a simple root of `f`, the
residual of the base member is nonzero at `a` — differentiating the pencil identity gives
`u_τ(a)·W₀(a) = -f'(a)`. -/
theorem eval_pencilW₀_ne_zero_of_deriv (hu : uτ.Monic) (hne : uτ.eval a ≠ 0)
    (hd : uτ ∣ vτ ^ 2 - f) (ha : f.eval a = 0) (ha' : f.derivative.eval a ≠ 0) :
    (pencilW₀ f uτ vτ a 0).eval a ≠ 0 := by
  have hb : (0 : K) ^ 2 = f.eval a := by rw [ha]; ring
  have hV₀ : (pencilV₀ uτ vτ a 0).eval a = 0 := eval_pencilV₀ hne
  have hU : (pencilU uτ a).eval a = 0 := by rw [eval_pencilU]; ring
  have hUder : (pencilU uτ a).derivative.eval a = uτ.eval a := by
    rw [pencilU, derivative_mul]
    simp
  have hkey := congrArg (fun p : K[X] ↦ p.derivative.eval a) (pencilW₀_spec (b := 0) hu hne hd hb)
  simp only [derivative_sub, derivative_pow, derivative_mul, eval_sub, eval_mul, eval_add,
    hV₀, hU, hUder, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at hkey
  intro h0
  rw [h0] at hkey
  exact ha' (by linear_combination -hkey)

/-- **The residual at a nonsingular centre is a nonzero polynomial in the parameter**: for
`b ≠ 0` its linear coefficient `2b` is nonzero, and for `b = 0` with `a` a simple root of
`f` it is a nonzero constant. This makes centre-transversality a finite condition on the
parameter uniformly over nonsingular centres. -/
theorem pencilPar_ne_zero_of_nonsingular [NeZero (2 : K)] (hu : uτ.Monic)
    (hne : uτ.eval a ≠ 0) (hd : uτ ∣ vτ ^ 2 - f) (hb : b ^ 2 = f.eval a)
    (hns : b ≠ 0 ∨ f.derivative.eval a ≠ 0) :
    pencilPar f uτ vτ a b a ≠ 0 := by
  rcases eq_or_ne b 0 with rfl | hb0
  · exact fun h0 ↦ eval_pencilW₀_ne_zero_of_deriv hu hne hd (by rw [← hb]; ring)
      (hns.resolve_left fun h ↦ h rfl) (by simpa using congrArg (eval 0) h0)
  · exact pencilPar_ne_zero_of_pencilV₀ (by rw [eval_pencilV₀ hne]; exact hb0)

/-- For a fixed `x`, only finitely many members of the pencil have `x` in their residual —
as soon as the residual is not identically `0` in the parameter. -/
theorem finite_setOf_eval_pencilW_eq_zero (h : pencilPar f uτ vτ a b x ≠ 0) :
    {t : K | (pencilW f uτ vτ a b t).eval x = 0}.Finite :=
  (Polynomial.finite_setOfPred_isRoot h).subset fun t ht ↦ by simpa [IsRoot] using ht

/-- For a fixed `x` off the modulus, exactly one member of the pencil vanishes at `x`. -/
theorem finite_setOf_eval_pencilV_eq_zero (hx : (pencilU uτ a).eval x ≠ 0) :
    {t : K | (pencilV uτ vτ a b t).eval x = 0}.Finite := by
  refine (Set.finite_singleton
    (-(pencilV₀ uτ vτ a b).eval x / (pencilU uτ a).eval x)).subset fun t ht ↦ ?_
  simp only [Set.mem_ofPred_eq, eval_pencilV] at ht
  rw [Set.mem_singleton_iff, eq_div_iff hx]
  linear_combination ht

/-- The `y`-coefficient of the tangency relation of the pencil. -/
noncomputable def pencilTangA (uτ vτ : K[X]) (a b : K) : K[X] :=
  2 * ((pencilV₀ uτ vτ a b).derivative * pencilU uτ a
    - pencilV₀ uτ vτ a b * (pencilU uτ a).derivative)

/-- The constant coefficient of the tangency relation of the pencil; it does not depend on
the member. -/
noncomputable def pencilTangB (f uτ : K[X]) (a : K) : K[X] :=
  2 * f * (pencilU uτ a).derivative - f.derivative * pencilU uτ a

/-- The top coefficient of `B` is the difference of the *integers* `2(g+1)` and `2g+1`,
hence `1` in every characteristic — also where `f'` or the derivative of the modulus drops
degree. -/
theorem coeff_pencilTangB (hf : f.Monic) (hu : uτ.Monic) {g : ℕ}
    (hfdeg : f.natDegree = 2 * g + 1) (hn : uτ.natDegree = g) :
    (pencilTangB f uτ a).coeff (3 * g + 1) = 1 := by
  have hN : (pencilU uτ a).Monic := pencilU_monic hu
  have hNdeg : (pencilU uτ a).natDegree = g + 1 := by rw [natDegree_pencilU hu, hn]
  have hfc : f.coeff (2 * g + 1) = 1 := by rw [← hfdeg, ← leadingCoeff, hf.leadingCoeff]
  have hNc : (pencilU uτ a).coeff (g + 1) = 1 := by rw [← hNdeg, ← leadingCoeff, hN.leadingCoeff]
  have h1 : (2 * f * (pencilU uτ a).derivative).coeff (3 * g + 1) = 2 * ((g : K) + 1) := by
    rw [show 3 * g + 1 = 2 * g + 1 + g by lia,
      coeff_mul_add_eq_of_natDegree_le
        (natDegree_mul_le.trans (by simp [hfdeg]))
        ((natDegree_derivative_le _).trans (by rw [hNdeg]; lia)),
      coeff_derivative, hNc, one_mul]
    simp [hfc]
  have h2 : (f.derivative * pencilU uτ a).coeff (3 * g + 1) = 2 * (g : K) + 1 := by
    rw [show 3 * g + 1 = 2 * g + (g + 1) by lia,
      coeff_mul_add_eq_of_natDegree_le
        ((natDegree_derivative_le _).trans (by rw [hfdeg]; lia)) hNdeg.le,
      coeff_derivative, hNc, mul_one, hfc, one_mul]
    push_cast
    ring
  rw [pencilTangB, coeff_sub, h1, h2]
  ring

theorem pencilTangB_ne_zero (hf : f.Monic) (hu : uτ.Monic) {g : ℕ}
    (hfdeg : f.natDegree = 2 * g + 1) (hn : uτ.natDegree = g) : pencilTangB f uτ a ≠ 0 :=
  fun h0 ↦ by simpa [h0] using coeff_pencilTangB (a := a) hf hu hfdeg hn

/-- A root of the residual is the `x`-coordinate of a point of the curve lying on the
member: this is how the auxiliary point `Q` is recovered from the parameter. -/
theorem eval_pencilV_sq (hu : uτ.Monic) (hne : uτ.eval a ≠ 0) (hd : uτ ∣ vτ ^ 2 - f)
    (hb : b ^ 2 = f.eval a) (h1 : (pencilW f uτ vτ a b t).eval x = 0) :
    (pencilV uτ vτ a b t).eval x ^ 2 = f.eval x := by
  have h := congrArg (eval x) (pencilW_spec (t := t) hu hne hd hb)
  simp only [eval_sub, eval_mul, eval_pow] at h
  rw [h1, mul_zero] at h
  linear_combination h

/-- **The tangency relation**: at a multiple root of the residual lying off the base locus,
the point of the curve on the member lies on the line `B + A·y = 0`. -/
theorem eval_pencilTang_eq_zero (hu : uτ.Monic) (hne : uτ.eval a ≠ 0) (hd : uτ ∣ vτ ^ 2 - f)
    (hb : b ^ 2 = f.eval a) (h1 : (pencilW f uτ vτ a b t).eval x = 0)
    (h2 : (pencilW f uτ vτ a b t).derivative.eval x = 0) :
    (pencilTangB f uτ a).eval x
      + (pencilTangA uτ vτ a b).eval x * (pencilV uτ vτ a b t).eval x = 0 := by
  have hy2 := eval_pencilV_sq hu hne hd hb h1
  rw [eval_pencilV] at hy2
  have hder : 2 * pencilV uτ vτ a b t * (pencilV uτ vτ a b t).derivative - f.derivative
      = (pencilU uτ a).derivative * pencilW f uτ vτ a b t
        + pencilU uτ a * (pencilW f uτ vτ a b t).derivative := by
    have h := congrArg derivative (pencilW_spec (t := t) hu hne hd hb)
    simp only [derivative_sub, derivative_mul, derivative_pow, Nat.cast_ofNat,
      Nat.add_one_sub_one, pow_one, map_ofNat] at h
    linear_combination h
  have hd2 : 2 * ((pencilV₀ uτ vτ a b).eval x + t * (pencilU uτ a).eval x)
      * ((pencilV₀ uτ vτ a b).derivative.eval x + t * (pencilU uτ a).derivative.eval x)
      = f.derivative.eval x := by
    have := congrArg (eval x) hder
    simp only [eval_sub, eval_add, eval_mul, eval_ofNat, derivative_pencilV, eval_pencilV,
      eval_C] at this
    rw [h1, h2] at this
    linear_combination this
  simp only [pencilTangA, pencilTangB, eval_sub, eval_mul, eval_ofNat, eval_pencilV]
  linear_combination (-2 * (pencilU uτ a).derivative.eval x) * hy2
    + (pencilU uτ a).eval x * hd2

/-- **Only finitely many members of the pencil are tangent to the curve away from the base
locus**: a tangency at `x` puts the point `(x, V_t(x))` of the curve on the line
`B + A·y = 0`, of which there are finitely many
(`ChabautyColeman.finite_curve_zeros`), and over each of their `x`-coordinates the
parameter satisfies a nonzero quadratic. -/
theorem finite_setOf_pencil_multiple_root (hf : f.Monic) (hu : uτ.Monic) (hne : uτ.eval a ≠ 0)
    (hd : uτ ∣ vτ ^ 2 - f) (hb : b ^ 2 = f.eval a) {g : ℕ} (hfdeg : f.natDegree = 2 * g + 1)
    (hn : uτ.natDegree = g) :
    {t : K | ∃ x, (pencilU uτ a).eval x ≠ 0 ∧ (pencilW f uτ vτ a b t).eval x = 0
      ∧ (pencilW f uτ vτ a b t).derivative.eval x = 0}.Finite := by
  have hbad := finite_curve_zeros (g₀ := pencilTangB f uτ a) (g₁ := pencilTangA uτ vτ a b)
    hf (by rw [hfdeg]; exact ⟨g, by lia⟩) (Or.inl (pencilTangB_ne_zero hf hu hfdeg hn))
  refine (((hbad.image Prod.fst).inter_of_left {x : K | (pencilU uτ a).eval x ≠ 0}).biUnion
    fun x hx ↦ finite_setOf_eval_pencilW_eq_zero
      (pencilPar_ne_zero_of_pencilU (f := f) (vτ := vτ) (b := b) hx.2)).subset ?_
  intro t ⟨x, hx, h1, h2⟩
  exact Set.mem_biUnion ⟨⟨(x, (pencilV uτ vτ a b t).eval x),
    ⟨eval_pencilV_sq hu hne hd hb h1, eval_pencilTang_eq_zero hu hne hd hb h1 h2⟩, rfl⟩, hx⟩ h1

/-- The residual of a nondegenerate member has the degree of the base divisor. -/
theorem natDegree_pencilW (ht : t ≠ 0) (hu : uτ.Monic) (hne : uτ.eval a ≠ 0)
    (hd : uτ ∣ vτ ^ 2 - f) (hb : b ^ 2 = f.eval a) (hv : vτ.degree < uτ.degree)
    (hfdeg : f.natDegree = 2 * uτ.natDegree + 1) :
    (pencilW f uτ vτ a b t).natDegree = uτ.natDegree + 1 := by
  have h₀ := natDegree_pencilW₀ (b := b) hu hne hd hb hv (by lia)
  have hV₀ := natDegree_pencilV₀_le (a := a) (b := b) hv
  have hlead : (C t ^ 2 * pencilU uτ a).natDegree = uτ.natDegree + 1 := by
    rw [← C_pow, natDegree_C_mul (pow_ne_zero 2 ht), natDegree_pencilU hu]
  have h2t : (2 * C t : K[X]).natDegree = 0 := by
    rw [show (2 * C t : K[X]) = C (2 * t) by rw [C_mul, map_ofNat], natDegree_C]
  have hmid : (2 * C t * pencilV₀ uτ vτ a b).natDegree ≤ uτ.natDegree :=
    natDegree_mul_le.trans (by rw [h2t]; simpa using hV₀)
  have hsum : (C t ^ 2 * pencilU uτ a + 2 * C t * pencilV₀ uτ vτ a b).natDegree
      = uτ.natDegree + 1 := by
    rw [natDegree_add_eq_left_of_natDegree_lt (by lia), hlead]
  rw [pencilW, natDegree_add_eq_left_of_natDegree_lt (by rw [hsum]; lia), hsum]

/-- **The base member of the pencil is nonzero at the roots of `u_τ`**: at such a root `r` the
value of `V₀` is that of `v_τ`, and `v_τ(r) = 0` would make `r` a common root of `u_τ` and `f`.
This keeps the pencil parameter well defined at every root of `u_τ`. -/
theorem eval_pencilV₀_ne_zero_of_isRoot (hd : uτ ∣ vτ ^ 2 - f) (hgp : IsCoprime uτ f) {r : K}
    (hr : uτ.eval r = 0) :
    (pencilV₀ uτ vτ a b).eval r ≠ 0 := fun h0 ↦ by
  obtain ⟨c, hc⟩ := dvd_pencilV₀_sub (uτ := uτ) (vτ := vτ) (a := a) (b := b)
  obtain ⟨w, hw⟩ := hd
  obtain ⟨p, q, hpq⟩ := hgp
  have hvr : vτ.eval r = 0 := by
    have := congrArg (eval r) hc
    simp only [eval_sub, eval_mul, hr, zero_mul, h0] at this
    linear_combination -this
  have hfr : f.eval r = 0 := by
    have := congrArg (eval r) hw
    simp only [eval_sub, eval_pow, eval_mul, hr, zero_mul, hvr] at this
    linear_combination -this
  simpa [hr, hfr] using congrArg (eval r) hpq

/-- **A good pencil parameter exists**: over an algebraically closed field, at a nonsingular
centre — `b ≠ 0`, or `a` a simple root of `f` — the parameter can be chosen, and the
auxiliary point `Q` taken to be any root of the residual, so that the member has top degree,
its residual is coprime to the base divisor and to `f`, and it meets the curve transversally
at `Q`. These are exactly the genericity conditions of the per-disk configuration. The
curve-avoidance clause is restricted to the roots of `f` other than `a` (for `b ≠ 0` no root
of `f` lies at `a`, so nothing is lost). -/
theorem exists_pencil_param [IsAlgClosed K] [NeZero (2 : K)] (hf : f.Monic) (hu : uτ.Monic)
    (hne : uτ.eval a ≠ 0) (hd : uτ ∣ vτ ^ 2 - f) (hb : b ^ 2 = f.eval a)
    (hns : b ≠ 0 ∨ f.derivative.eval a ≠ 0)
    (hv : vτ.degree < uτ.degree) (hgp : IsCoprime uτ f) {g : ℕ}
    (hfdeg : f.natDegree = 2 * g + 1) (hn : uτ.natDegree = g) :
    ∃ t x : K, t ≠ 0 ∧ (pencilU uτ a).eval x ≠ 0 ∧ (pencilW f uτ vτ a b t).eval x = 0
      ∧ (pencilW f uτ vτ a b t).eval a ≠ 0
      ∧ (pencilW f uτ vτ a b t).derivative.eval x ≠ 0
      ∧ ∀ r, f.eval r = 0 → r ≠ a → (pencilV uτ vτ a b t).eval r ≠ 0 := by
  have hcop r (hr : uτ.eval r = 0) (hfr : f.eval r = 0) : False := by
    obtain ⟨p, q, hpq⟩ := hgp
    simpa [hr, hfr] using congrArg (eval r) hpq
  have hUf r (hr : f.eval r = 0) (hra : r ≠ a) : (pencilU uτ a).eval r ≠ 0 := by
    rw [eval_pencilU]
    exact mul_ne_zero (fun h0 ↦ hcop r h0 hr) (sub_ne_zero.mpr hra)
  have h1 : {t : K | (pencilW f uτ vτ a b t).eval a = 0}.Finite :=
    finite_setOf_eval_pencilW_eq_zero (pencilPar_ne_zero_of_nonsingular hu hne hd hb hns)
  have h2 : (⋃ r ∈ {r : K | uτ.IsRoot r},
      {t : K | (pencilW f uτ vτ a b t).eval r = 0}).Finite :=
    (finite_setOfPred_isRoot hu.ne_zero).biUnion fun r hr ↦
      finite_setOf_eval_pencilW_eq_zero
        (pencilPar_ne_zero_of_pencilV₀ (eval_pencilV₀_ne_zero_of_isRoot hd hgp hr))
  have h3 : (⋃ r ∈ {r : K | f.IsRoot r ∧ r ≠ a},
      {t : K | (pencilV uτ vτ a b t).eval r = 0}).Finite :=
    ((finite_setOfPred_isRoot hf.ne_zero).subset (Set.sep_subset _ _)).biUnion
      fun r hr ↦ finite_setOf_eval_pencilV_eq_zero (hUf r hr.1 hr.2)
  have h4 := finite_setOf_pencil_multiple_root hf hu hne hd hb hfdeg hn
  have hbad : {t : K | t = 0 ∨ (pencilW f uτ vτ a b t).eval a = 0
      ∨ (∃ r, uτ.IsRoot r ∧ (pencilW f uτ vτ a b t).eval r = 0)
      ∨ (∃ r, f.IsRoot r ∧ r ≠ a ∧ (pencilV uτ vτ a b t).eval r = 0)
      ∨ (∃ x, (pencilU uτ a).eval x ≠ 0 ∧ (pencilW f uτ vτ a b t).eval x = 0
          ∧ (pencilW f uτ vτ a b t).derivative.eval x = 0)}.Finite := by
    refine (((((Set.finite_singleton (0 : K)).union h1).union h2).union h3).union
      h4).subset fun t ht ↦ ?_
    rcases ht with h | h | ⟨r, hr, h⟩ | ⟨r, hr, hra, h⟩ | h
    exacts [.inl (.inl (.inl (.inl h))), .inl (.inl (.inl (.inr h))),
      .inl (.inl (.inr (Set.mem_biUnion hr h))),
      .inl (.inr (Set.mem_biUnion (Set.mem_sep hr hra) h)), .inr h]
  obtain ⟨t, ht⟩ := hbad.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_or, not_exists, not_and] at ht
  obtain ⟨ht0, hta, htu, htf, httang⟩ := ht
  have hWdeg : (pencilW f uτ vτ a b t).natDegree = g + 1 := by
    rw [natDegree_pencilW ht0 hu hne hd hb hv (by rw [hfdeg, hn]), hn]
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (pencilW f uτ vτ a b t)
    (natDegree_pos_iff_degree_pos.mp (by lia)).ne'
  have hxU : (pencilU uτ a).eval x ≠ 0 := by
    rw [eval_pencilU]
    exact mul_ne_zero (fun h0 ↦ htu x h0 hx) (sub_ne_zero.mpr fun h0 ↦ hta (h0 ▸ hx))
  exact ⟨t, x, ht0, hxU, hx, hta, httang x hxU hx, htf⟩

end Pencil

end ChabautyColeman

end
