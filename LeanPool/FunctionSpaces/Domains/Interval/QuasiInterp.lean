/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Interval.Splines
public import LeanPool.FunctionSpaces.Domains.Interval.LocalProjection

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# A spline quasi-interpolant

The **quasi-interpolant** of level `k` is `Q_k g = ∑_n λ_n(g) N_r(2^k x - n)`, summed over the
B-splines `-r < n < N` that meet `[0, N 2^(-k))` (`Interval.qiPieces`); on `[0, 1)` the index bound
is `N = 2^k`, and larger `N` serve periodic extensions. Its coefficient
`λ_n(g) = c_n(Π g(· 2^(-k)))` (`Interval.qiCoeff`) is the B-spline coefficient (Marsden's identity,
`Interval.polyFun_eq_sum_bsplineCoef`) of the local projection `Π g` of `g` on one interval
`J(n) = I_{k, max(n, 0)}` of the support of `N_r(2^k x - n)` in `[0, 1)`.

* `Q_k g` is a spline, with joins at every knot (`Interval.qiPieces_join`).
* **Local reproduction**: if `g` is a polynomial `T` of degree `< r` on the intervals `J(n)`,
  `i - r < n ≤ i`, then `Q_k g = T` on `I_{k,i}` (`Interval.polyFun_qiPieces_of_eq`): the local
  projections reproduce `T`, so the coefficients are those of `T`, and Marsden's identity sums
  them back to `T`.
* **Reproduction of splines**: `Q_k s = s` for every spline `s` of order `r` and level `k`
  (`Interval.ppFun_qiPieces_ppFun`), since the pieces of `s` in the support of a B-spline have the
  same coefficient for it (`Interval.bsplineCoef_comp_eq_of_splineJoins`). So the B-splines
  `N_r(2^k x - n)`, `-r < n < 2^k`, span the splines on `[0, 1)`
  (`Interval.ppFun_eq_sum_bsplinePieces`).
* **Local bounds**: `|λ_n(g)| ≤ C 2^(k/p) ‖g‖_{L_p(J(n))}` (`Interval.enorm_qiCoeff_le`), since the
  coordinates in the B-spline basis are bounded functionals on the polynomials
  (`Interval.exists_enorm_bcoord_le`) and the local projection is bounded, and hence
  `‖Q_k g‖_{L_p(I_{k,i})} ≤ C ∑_{i - r < n ≤ i} ‖g‖_{L_p(J(n))}` (`Interval.eLpNorm_qiPieces_le`).
-/

@[expose] public section

open MeasureTheory Set Polynomial
open scoped ENNReal

namespace Interval

/-- Two polynomials with the same values at all real points are equal. -/
theorem eq_of_polyFun_eq {P Q : ℂ[X]} (h : ∀ x : ℝ, polyFun P x = polyFun Q x) : P = Q := by
  refine Polynomial.eq_of_infinite_eval_eq P Q ?_
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective Complex.ofReal_injective)
  rintro _ ⟨x, rfl⟩
  exact h x

/-- The local projection on `I_{k,m}` in the coordinate `y = 2^k x`. -/
noncomputable def locProjScaled (r k : ℕ) (g : ℝ → ℂ) (m : ℕ) : ℂ[X] :=
  (locProj r k g m).comp (C (((0 : ℝ) : ℝ) : ℂ) + C (((1 / 2 ^ k : ℝ) : ℝ) : ℂ) * X)

/-- The indices `-r < n < N` of the B-splines of level `k` that meet `[0, N 2^(-k))`. -/
def qiIdx (r N : ℕ) : Finset ℤ := Finset.Ioo (-(r : ℤ)) N

/-- The **quasi-interpolant coefficients** `λ_n(g) = c_n(Π_{k, J(n)} g(· 2^(-k)))`, with
`J(n) = I_{k, max(n, 0)}`. -/
noncomputable def qiCoeff {r : ℕ} (hr : 1 ≤ r) (k : ℕ) (g : ℝ → ℂ) (n : ℤ) : ℂ :=
  bsplineCoef hr (locProjScaled r k g n.toNat) n

/-- The pieces of the **quasi-interpolant** `Q_k g = ∑_n λ_n(g) N_r(2^k x - n)`. -/
noncomputable def qiPieces {r : ℕ} (hr : 1 ≤ r) (k N : ℕ) (g : ℝ → ℂ) : ℕ → ℂ[X] :=
  ∑ n ∈ qiIdx r N, fun m => C (qiCoeff hr k g n) * bsplinePieces r k n m

/-- The pieces of the quasi-interpolant. -/
theorem qiPieces_apply {r : ℕ} (hr : 1 ≤ r) (k N : ℕ) (g : ℝ → ℂ) (m : ℕ) :
    qiPieces hr k N g m = ∑ n ∈ qiIdx r N, C (qiCoeff hr k g n) * bsplinePieces r k n m := by
  rw [qiPieces, Finset.sum_apply]

/-- The quasi-interpolant has pieces of degree `< r`. -/
theorem qiPieces_mem {r : ℕ} (hr : 1 ≤ r) (k N : ℕ) (g : ℝ → ℂ) (m : ℕ) :
    qiPieces hr k N g m ∈ degreeLT ℂ r := by
  rw [qiPieces_apply]
  exact Submodule.sum_mem _ fun n _ => by
    rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (bsplinePieces_mem hr k n m)

/-- **The quasi-interpolant has spline joins at every knot** `m 2^(-k)`, `m ≥ 1`. -/
theorem qiPieces_join {r : ℕ} (hr : 1 ≤ r) (k N : ℕ) (g : ℝ → ℂ) {m : ℕ} (hm : 0 < m) :
    ∃ c : ℂ, qiPieces hr k N g m - qiPieces hr k N g (m - 1) =
      C c * (X - C ((((m : ℝ) / 2 ^ k : ℝ)) : ℂ)) ^ (r - 1) := by
  choose c hc using fun n : ℤ => bsplinePieces_join hr k n hm
  refine ⟨∑ n ∈ qiIdx r N, qiCoeff hr k g n * c n, ?_⟩
  rw [qiPieces_apply, qiPieces_apply, ← Finset.sum_sub_distrib, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← mul_sub, hc n, C_mul]
  ring

/-- **The quasi-interpolant is a spline.** -/
theorem splineJoins_qiPieces {r : ℕ} (hr : 1 ≤ r) (k N : ℕ) (g : ℝ → ℂ) :
    SplineJoins r k (qiPieces hr k N g) := fun _ hm _ => qiPieces_join hr k N g hm

/-- The values of the quasi-interpolant on `I_{k,m}`: `Q_k g(x) = ∑_n λ_n(g) N_r(2^k x - n)`. -/
theorem polyFun_qiPieces {r : ℕ} (hr : 1 ≤ r) (k N : ℕ) (g : ℝ → ℂ) {m : ℕ} {x : ℝ}
    (hx : x ∈ dyadicIco k m) :
    polyFun (qiPieces hr k N g m) x =
      ∑ n ∈ qiIdx r N, qiCoeff hr k g n * bspline r (2 ^ k * x - n) := by
  rw [qiPieces_apply, polyFun, eval_finsetSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [eval_mul, eval_C, ← polyFun, polyFun_bsplinePieces hr k n hx]

/-- On `I_{k,i}` only the B-splines `i - r < n ≤ i` are nonzero. -/
theorem bspline_eq_zero_of_not_mem {r k i : ℕ} {x : ℝ} (hx : x ∈ dyadicIco k i) {n : ℤ}
    (hn : ¬ ((i : ℤ) - r < n ∧ n ≤ i)) : bspline r (2 ^ k * x - n) = 0 := by
  rw [mem_dyadicIco] at hx
  rcases not_and_or.1 hn with h | h
  · apply bspline_eq_zero_of_ge
    have : (n : ℝ) ≤ (i : ℝ) - r := by exact_mod_cast (by omega : n ≤ (i : ℤ) - r)
    linarith [hx.1]
  · apply bspline_eq_zero_of_lt
    have : (i : ℝ) + 1 ≤ n := by exact_mod_cast (by omega : (i : ℤ) + 1 ≤ n)
    linarith [hx.2]

/-- **The quasi-interpolant from its coefficients**: if the coefficients `λ_n(g)`,
`i - r < n ≤ i`, are the B-spline coefficients `c_n` of `T(· 2^(-k))` for a polynomial `T` of
degree `< r`, then `Q_k g = T` on `I_{k,i}`, by Marsden's identity for `T(· 2^(-k))` on
`[i, i + 1)`. -/
theorem polyFun_qiPieces_of_coeff {r : ℕ} (hr : 1 ≤ r) {k N : ℕ} {g : ℝ → ℂ} {T : ℂ[X]}
    (hT : T ∈ degreeLT ℂ r) {i : ℕ} (hi : i < N)
    (hcoeff : ∀ n : ℤ, (i : ℤ) - r < n → n ≤ i → qiCoeff hr k g n =
      bsplineCoef hr (T.comp (C (((0 : ℝ) : ℝ) : ℂ) + C (((1 / 2 ^ k : ℝ) : ℝ) : ℂ) * X)) n)
    {x : ℝ} (hx : x ∈ dyadicIco k i) : polyFun (qiPieces hr k N g i) x = polyFun T x := by
  set Ts := T.comp (C (((0 : ℝ) : ℝ) : ℂ) + C (((1 / 2 ^ k : ℝ) : ℝ) : ℂ) * X)
  have hTs : Ts ∈ degreeLT ℂ r := comp_affine_mem_degreeLT hT _ _
  have hik : (i : ℤ) < N := by exact_mod_cast hi
  rw [polyFun_qiPieces hr k N g hx]
  -- only the B-splines `i - r < n ≤ i` contribute
  have hsub : ∑ n ∈ qiIdx r N, qiCoeff hr k g n * bspline r (2 ^ k * x - n) =
      ∑ n ∈ Finset.Ioc ((i : ℤ) - r) i, bsplineCoef hr Ts n * bspline r (2 ^ k * x - n) := by
    rw [← Finset.sum_subset (s₁ := Finset.Ioc ((i : ℤ) - r) i) (fun n hn => by
        rw [Finset.mem_Ioc] at hn
        rw [qiIdx, Finset.mem_Ioo]
        constructor <;> omega)
      (fun n _ hn => by
        rw [Finset.mem_Ioc] at hn
        simp [bspline_eq_zero_of_not_mem hx hn])]
    exact Finset.sum_congr rfl fun n hn => by
      rw [Finset.mem_Ioc] at hn
      rw [hcoeff n hn.1 hn.2]
  -- Marsden's identity for `T(· 2^(-k))` at `y = 2^k x ∈ [i, i + 1)`
  have hy : 2 ^ k * x ∈ Set.Ico ((i : ℤ) : ℝ) ((i : ℤ) + 1) := by
    rw [mem_dyadicIco] at hx
    push_cast
    exact hx
  have hM := polyFun_eq_sum_bsplineCoef hr hTs hy
  have hval : polyFun Ts (2 ^ k * x) = polyFun T x := by
    rw [polyFun_comp_affine, show (0 : ℝ) + 1 / 2 ^ k * (2 ^ k * x) = x by
      rw [zero_add]; field_simp]
  rw [hsub, ← hval, hM]
  -- reindex `n = i - j`
  refine Finset.sum_nbij' (fun n : ℤ => ((i : ℤ) - n).toNat) (fun j : ℕ => (i : ℤ) - j)
    ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Ioc, Finset.mem_range] at hn ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Ioc, Finset.mem_range] at hj ⊢
    omega
  · intro n hn
    simp only [Finset.mem_Ioc] at hn
    omega
  · intro j _
    simp
  · intro n hn
    simp only [Finset.mem_Ioc] at hn
    rw [show (i : ℤ) - (((i : ℤ) - n).toNat : ℤ) = n by omega]

/-- **Local reproduction of polynomials**: if `g = T` on the intervals `J(n)`, `i - r < n ≤ i`,
for a polynomial `T` of degree `< r`, then `Q_k g = T` on `I_{k,i}`: the local projections
reproduce `T`, so the coefficients are those of `T`. -/
theorem polyFun_qiPieces_of_eq {r : ℕ} (hr : 1 ≤ r) {k N : ℕ} {g : ℝ → ℂ} {T : ℂ[X]}
    (hT : T ∈ degreeLT ℂ r) {i : ℕ} (hi : i < N)
    (hg : ∀ n : ℤ, (i : ℤ) - r < n → n ≤ i → ∀ y ∈ dyadicIco k n.toNat, g y = polyFun T y)
    {x : ℝ} (hx : x ∈ dyadicIco k i) : polyFun (qiPieces hr k N g i) x = polyFun T x :=
  polyFun_qiPieces_of_coeff hr hT hi (fun n hn1 hn2 => by
    have hloc : locProj r k g n.toNat = T := eq_of_polyFun_eq fun y =>
      polyFun_locProj_of_eqOn hT (hg n hn1 hn2) y
    rw [qiCoeff, locProjScaled, hloc]) hx

/-! ### Reproduction of splines -/

/-- **The quasi-interpolant reproduces splines, piece by piece**: for a spline with pieces `Q_m` of
degree `< r`, `Q_k s = Q_i` on `I_{k,i}`. The coefficient `λ_n(s)` is `c_n` of the piece of `s` on
`J(n)`, and this is `c_n` of `Q_i` (`Interval.bsplineCoef_comp_eq_of_splineJoins`), since the
pieces between `J(n)` and `I_{k,i}` differ by powers `(x - m 2^(-k))^(r-1)` with `n < m < n + r`. -/
theorem polyFun_qiPieces_ppFun {r : ℕ} (hr : 1 ≤ r) {k : ℕ} {Q : ℕ → ℂ[X]}
    (hQ : ∀ m, Q m ∈ degreeLT ℂ r) (hJ : SplineJoins r k Q) {i : ℕ} (hi : i < 2 ^ k) {x : ℝ}
    (hx : x ∈ dyadicIco k i) :
    polyFun (qiPieces hr k (2 ^ k) (ppFun k Q) i) x = polyFun (Q i) x := by
  refine polyFun_qiPieces_of_coeff hr (hQ i) hi (fun n hn1 hn2 => ?_) hx
  have hn : n.toNat ≤ i := by omega
  have hloc : locProj r k (ppFun k Q) n.toNat = Q n.toNat := eq_of_polyFun_eq fun y =>
    polyFun_locProj_of_eqOn (hQ _) (fun z hz => ppFun_eq_of_mem Q (hn.trans_lt hi) hz) y
  rw [qiCoeff, locProjScaled, hloc]
  exact (bsplineCoef_comp_eq_of_splineJoins hr hQ hJ hn hi (Int.self_le_toNat n)
    (by omega)).symm

/-- **The quasi-interpolant is a projection onto the splines**: `Q_k s = s` for every spline `s` of
order `r` and level `k` on `[0, 1)`. -/
theorem ppFun_qiPieces_ppFun {r : ℕ} (hr : 1 ≤ r) {k : ℕ} {Q : ℕ → ℂ[X]}
    (hQ : ∀ m, Q m ∈ degreeLT ℂ r) (hJ : SplineJoins r k Q) :
    ppFun k (qiPieces hr k (2 ^ k) (ppFun k Q)) = ppFun k Q := by
  funext x
  by_cases hx : x ∈ Ico (0 : ℝ) 1
  · obtain ⟨h1, h1'⟩ := mem_dyadicIco_floor (k := k) hx
    rw [ppFun_eq_of_mem _ h1' h1, ppFun_eq_of_mem _ h1' h1, polyFun_qiPieces_ppFun hr hQ hJ h1' h1]
  · rw [ppFun_eq_zero _ hx, ppFun_eq_zero _ hx]

/-- **The B-splines span the splines**: every spline of order `r` and level `k` on `[0, 1)` is
`∑_n λ_n N_r(2^k x - n)`, summed over the B-splines `-r < n < 2^k` that meet `[0, 1)`, with the
quasi-interpolant coefficients `λ_n`. -/
theorem ppFun_eq_sum_bsplinePieces {r : ℕ} (hr : 1 ≤ r) {k : ℕ} {Q : ℕ → ℂ[X]}
    (hQ : ∀ m, Q m ∈ degreeLT ℂ r) (hJ : SplineJoins r k Q) :
    ppFun k Q = ∑ n ∈ qiIdx r (2 ^ k),
      fun x => qiCoeff hr k (ppFun k Q) n * ppFun k (bsplinePieces r k n) x := by
  conv_lhs => rw [← ppFun_qiPieces_ppFun hr hQ hJ]
  rw [qiPieces, ppFun_sum]
  exact Finset.sum_congr rfl fun n _ => ppFun_const_mul k _ _

/-! ### Bounds -/

/-- The B-spline is bounded. -/
theorem exists_enorm_bspline_le (r : ℕ) : ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ y, ‖bspline r y‖ₑ ≤ M := by
  obtain ⟨M, hM, hMb⟩ := exists_enorm_polyFun_le_of_fintype
    (fun j : Fin r => bsplineLocal r j)
  refine ⟨M, hM, fun y => ?_⟩
  by_cases hy : 0 ≤ y ∧ y < r
  · have hj : ⌊y⌋₊ < r := (Nat.floor_lt hy.1).2 hy.2
    have hmem : y ∈ Ico (⌊y⌋₊ : ℝ) (⌊y⌋₊ + 1) := ⟨Nat.floor_le hy.1, Nat.lt_floor_add_one y⟩
    rw [bspline_eq_piece hj hmem]
    have h := hMb ⟨⌊y⌋₊, hj⟩ (y - ⌊y⌋₊) ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
    simp only [bsplineLocal, polyFun, eval_comp, eval_add, eval_X, eval_C] at h
    simp only [polyFun]
    convert h using 2
    push_cast
    ring_nf
  · simp only [bspline, hy, ↓reduceIte, eNorm_zero, zero_le]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (p) in
/-- **The B-spline coordinates are bounded functionals**: there is `C` with
`|a_j(R)| ≤ C ‖R‖_{L_p[0,1]}` for every polynomial `R` of degree `< r` (finite dimension). -/
theorem exists_enorm_bcoord_le {r : ℕ} (hr : 1 ≤ r) :
    ∃ Cb : ℝ≥0∞, Cb ≠ ∞ ∧ ∀ R ∈ degreeLT ℂ r, ∀ j : ℕ,
      ‖bcoord hr R j‖ₑ ≤ Cb * eLpNorm (polyFun R) p (volume.restrict (Icc 0 1)) := by
  obtain ⟨K, -, hK⟩ := (coeffToLp p r 0 1).injective_iff_antilipschitz.1
    (coeffToLp_injective r zero_lt_one)
  let T : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) :=
    (bsplineBasis hr).equivFun.toLinearMap ∘ₗ (degreeLTEquiv ℂ r).symm.toLinearMap
  let T' := LinearMap.toContinuousLinearMap T
  refine ⟨‖T'‖ₑ * K, ENNReal.mul_ne_top eNorm_ne_top ENNReal.coe_ne_top, fun R hR j => ?_⟩
  by_cases hj : j < r
  · set c := degreeLTEquiv ℂ r ⟨R, hR⟩
    have hRc : (degreeLTEquiv ℂ r).symm c = ⟨R, hR⟩ := by simp [c]
    have hbc : bcoord hr R j = T c ⟨j, hj⟩ := by
      have h : R ∈ degreeLT ℂ r ∧ j < r := ⟨hR, hj⟩
      simp only [bcoord, h, and_self, ↓reduceDIte, T, LinearMap.coe_comp, LinearEquiv.coe_coe,
        Function.comp_apply, hRc, Module.Basis.equivFun_apply]
    have h1 : ‖T c ⟨j, hj⟩‖ ≤ ‖T c‖ := norm_le_pi_norm _ _
    have h2 : ‖T c‖ ≤ ‖T'‖ * ‖c‖ := T'.le_opNorm c
    have h3 : ‖c‖ ≤ K * ‖coeffToLp p r 0 1 c‖ := ZeroHomClass.bound_of_antilipschitz _ hK c
    have hreal : ‖bcoord hr R j‖ ≤ ‖T'‖ * (K * ‖coeffToLp p r 0 1 c‖) := by
      rw [hbc]
      exact h1.trans (h2.trans (by gcongr))
    have hnorm : ‖coeffToLp p r 0 1 c‖ₑ = eLpNorm (polyFun R) p (volume.restrict (Icc 0 1)) := by
      rw [enorm_coeffToLp, hRc]
    rw [← hnorm, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm]
    calc ENNReal.ofReal ‖bcoord hr R j‖
        ≤ ENNReal.ofReal (‖T'‖ * (K * ‖coeffToLp p r 0 1 c‖)) := ENNReal.ofReal_le_ofReal hreal
      _ = _ := by
        rw [ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (NNReal.coe_nonneg _),
          ENNReal.ofReal_coe_nnreal]
        ring
  · have h : ¬ (R ∈ degreeLT ℂ r ∧ j < r) := fun h => hj h.2
    simp only [bcoord, h, ↓reduceDIte, eNorm_zero, zero_le]

/-- The quasi-interpolant coefficient as a coordinate on the unit interval of `J(n)`:
`λ_n(g) = a_{max(n,0) - n}(Π g((· + max(n, 0)) 2^(-k)))`. -/
theorem qiCoeff_eq_bcoord {r : ℕ} (hr : 1 ≤ r) (k : ℕ) (g : ℝ → ℂ) {n : ℤ} (hn : -(r : ℤ) < n) :
    qiCoeff hr k g n = bcoord hr ((locProjScaled r k g n.toNat).comp
      (X + C (((n.toNat : ℤ) : ℂ)))) ((n.toNat : ℤ) - n).toNat := by
  have hmem : locProjScaled r k g n.toNat ∈ degreeLT ℂ r :=
    comp_affine_mem_degreeLT (locProj_mem r k g _) _ _
  rw [bcoord_comp_eq_bsplineCoef hr hmem _ (by omega), qiCoeff]
  congr 1
  omega

/-- **The quasi-interpolant coefficients are bounded by the local `L_p` norm**:
`|λ_n(g)| ≤ C_b r M² 2^(k/p) ‖g‖_{L_p(J(n))}`. -/
theorem enorm_qiCoeff_le {r : ℕ} (hr : 1 ≤ r) {Cb : ℝ≥0∞}
    (hCb : ∀ R ∈ degreeLT ℂ r, ∀ j : ℕ,
      ‖bcoord hr R j‖ₑ ≤ Cb * eLpNorm (polyFun R) p (volume.restrict (Icc 0 1)))
    (hp : p ≠ ∞) (k : ℕ) {g : ℝ → ℂ} {n : ℤ} (hn : -(r : ℤ) < n)
    (hg : AEStronglyMeasurable g (volume.restrict (dyadicIco k n.toNat))) :
    ‖qiCoeff hr k g n‖ₑ ≤ Cb * ppProjConst r * ENNReal.ofReal (2 ^ k) ^ (1 / p.toReal) *
      eLpNorm g p (volume.restrict (dyadicIco k n.toNat)) := by
  have hL : (0 : ℝ) < 1 / 2 ^ k := by positivity
  set m := n.toNat
  set R := (locProjScaled r k g m).comp (X + C (((m : ℤ) : ℂ)))
  have hR : R ∈ degreeLT ℂ r := comp_X_add_C_mem
    (comp_affine_mem_degreeLT (locProj_mem r k g _) _ _) _
  have hRfun : polyFun R = fun t => polyFun (locProj r k g m) ((m : ℝ) / 2 ^ k + 1 / 2 ^ k * t)
    := by
    funext t
    simp only [R, locProjScaled, polyFun, eval_comp, eval_add, eval_mul, eval_X, eval_C]
    congr 1
    push_cast
    ring
  have hnorm : eLpNorm (polyFun R) p (volume.restrict (Icc 0 1)) =
      ENNReal.ofReal (2 ^ k) ^ (1 / p.toReal) *
        eLpNorm (polyFun (locProj r k g m)) p (volume.restrict (dyadicIco k m)) := by
    rw [hRfun, eLpNorm_comp_affine (measurable_polyFun _) hp _ hL, mul_zero, add_zero, mul_one,
      one_div ((2 : ℝ) ^ k), inv_inv, dyadicIco]
    congr 2
    rw [show (m : ℝ) / 2 ^ k + (2 ^ k)⁻¹ = (m + 1) / 2 ^ k by field_simp]
    exact (Measure.restrict_congr_set Ico_ae_eq_Icc).symm
  rw [qiCoeff_eq_bcoord hr k g hn]
  refine (hCb R hR _).trans ?_
  rw [hnorm]
  calc Cb * (ENNReal.ofReal (2 ^ k) ^ (1 / p.toReal) *
        eLpNorm (polyFun (locProj r k g m)) p (volume.restrict (dyadicIco k m)))
      ≤ Cb * (ENNReal.ofReal (2 ^ k) ^ (1 / p.toReal) *
          (ppProjConst r * eLpNorm g p (volume.restrict (dyadicIco k m)))) := by
        gcongr
        exact eLpNorm_locProj_le (enorm_monoBasis_le r) (enorm_dualPoly_le r) Fact.out k m hg
    _ = _ := by ring

/-- On `I_{k,m}` only the B-splines `m - r < n ≤ m` have nonzero pieces; the piece with
`m - n = r` is `B_r = 0` (`Interval.bsplinePiece_top`). -/
theorem bsplinePieces_eq_zero_of_not_mem {r : ℕ} (hr : 1 ≤ r) (k : ℕ) {n : ℤ} {m : ℕ}
    (hn : ¬ ((m : ℤ) - r < n ∧ n ≤ m)) : bsplinePieces r k n m = 0 := by
  unfold bsplinePieces
  split_ifs with h
  · rw [show ((m : ℤ) - n).toNat = r by omega, bsplinePiece_top hr, zero_comp]
  · rfl

/-- The pieces of the quasi-interpolant on `I_{k,i}`, `i < N`, as the sum over the B-splines
`i - r < n ≤ i`. -/
theorem qiPieces_eq_sum_Ioc {r : ℕ} (hr : 1 ≤ r) (k : ℕ) {N i : ℕ} (hi : i < N) (g : ℝ → ℂ) :
    qiPieces hr k N g i =
      ∑ n ∈ Finset.Ioc ((i : ℤ) - r) i, C (qiCoeff hr k g n) * bsplinePieces r k n i := by
  have hik : (i : ℤ) < N := by exact_mod_cast hi
  rw [qiPieces_apply]
  exact (Finset.sum_subset (fun n hn => by
      rw [Finset.mem_Ioc] at hn
      rw [qiIdx, Finset.mem_Ioo]
      constructor <;> omega)
    (fun n _ hn => by
      rw [Finset.mem_Ioc] at hn
      rw [bsplinePieces_eq_zero_of_not_mem hr k hn, mul_zero])).symm

/-- On `I_{k,i}` the quasi-interpolant is the sum over the B-splines `i - r < n ≤ i`. -/
theorem polyFun_qiPieces_eq_sum_Ioc {r : ℕ} (hr : 1 ≤ r) {k N i : ℕ} (hi : i < N)
    (g : ℝ → ℂ) {x : ℝ} (hx : x ∈ dyadicIco k i) :
    polyFun (qiPieces hr k N g i) x =
      ∑ n ∈ Finset.Ioc ((i : ℤ) - r) i, qiCoeff hr k g n * bspline r (2 ^ k * x - n) := by
  have hik : (i : ℤ) < N := by exact_mod_cast hi
  rw [polyFun_qiPieces hr k N g hx]
  exact (Finset.sum_subset (fun n hn => by
      rw [Finset.mem_Ioc] at hn
      rw [qiIdx, Finset.mem_Ioo]
      constructor <;> omega)
    (fun n _ hn => by
      rw [Finset.mem_Ioc] at hn
      simp [bspline_eq_zero_of_not_mem hx hn])).symm

/-- **The quasi-interpolant is locally bounded**: on `I_{k,i}`,
`‖Q_k g‖_{L_p(I_{k,i})} ≤ M_N C_b r M² ∑_{i - r < n ≤ i} ‖g‖_{L_p(J(n))}`, with `M_N` a bound of
the B-spline. -/
theorem eLpNorm_qiPieces_le {r : ℕ} (hr : 1 ≤ r) {Cb : ℝ≥0∞}
    (hCb : ∀ R ∈ degreeLT ℂ r, ∀ j : ℕ,
      ‖bcoord hr R j‖ₑ ≤ Cb * eLpNorm (polyFun R) p (volume.restrict (Icc 0 1)))
    {MN : ℝ≥0∞} (hMN : ∀ y, ‖bspline r y‖ₑ ≤ MN) (hp : p ≠ ∞) {k N i : ℕ} (hi : i < N)
    {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) :
    eLpNorm (polyFun (qiPieces hr k N g i)) p (volume.restrict (dyadicIco k i)) ≤
      MN * (Cb * ppProjConst r) * ∑ n ∈ Finset.Ioc ((i : ℤ) - r) i,
        eLpNorm g p (volume.restrict (dyadicIco k n.toNat)) := by
  have hθ : 0 ≤ 1 / p.toReal := by positivity
  have hθ' : 1 / p.toReal = p.toReal⁻¹ := one_div _
  have hgI : ∀ n ∈ Finset.Ioc ((i : ℤ) - r) i,
      AEStronglyMeasurable g (volume.restrict (dyadicIco k n.toNat)) := fun _ _ => hg.restrict
  have hpt : ∀ x ∈ dyadicIco k i, ‖polyFun (qiPieces hr k N g i) x‖ₑ ≤
      MN * (Cb * ppProjConst r) * ENNReal.ofReal (2 ^ k) ^ (1 / p.toReal) *
        ∑ n ∈ Finset.Ioc ((i : ℤ) - r) i, eLpNorm g p (volume.restrict (dyadicIco k n.toNat)) :=
    fun x hx => by
      rw [polyFun_qiPieces_eq_sum_Ioc hr hi g hx]
      refine (eNorm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      have hn' := (Finset.mem_Ioc.1 hn).1
      rw [eNorm_mul]
      calc ‖qiCoeff hr k g n‖ₑ * ‖bspline r (2 ^ k * x - n)‖ₑ
          ≤ (Cb * ppProjConst r * ENNReal.ofReal (2 ^ k) ^ (1 / p.toReal) *
              eLpNorm g p (volume.restrict (dyadicIco k n.toNat))) * MN :=
            mul_le_mul' (enorm_qiCoeff_le hr hCb hp k (by omega) (hgI n hn)) (hMN _)
        _ = _ := by ring
  refine (eLpNorm_le_of_ae_eNorm_bound (measurable_polyFun _).aestronglyMeasurable
    ((ae_restrict_iff' (measurableSet_dyadicIco k i)).2 (Filter.Eventually.of_forall
      hpt))).trans_eq ?_
  rw [Measure.restrict_apply_univ, volume_dyadicIco, smul_eq_mul, ← hθ']
  have h1 : ENNReal.ofReal (2 ^ k) ^ (1 / p.toReal) * ENNReal.ofReal (1 / 2 ^ k) ^ (1 / p.toReal) =
      1 := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hθ, ← ENNReal.ofReal_mul (by positivity),
      mul_one_div_cancel (by positivity), ENNReal.ofReal_one, ENNReal.one_rpow]
  calc MN * (Cb * ppProjConst r) * ENNReal.ofReal (2 ^ k) ^ (1 / p.toReal) *
        (∑ n ∈ Finset.Ioc ((i : ℤ) - r) i, eLpNorm g p (volume.restrict (dyadicIco k n.toNat))) *
        ENNReal.ofReal (1 / 2 ^ k) ^ (1 / p.toReal)
      = MN * (Cb * ppProjConst r) * (ENNReal.ofReal (2 ^ k) ^ (1 / p.toReal) *
          ENNReal.ofReal (1 / 2 ^ k) ^ (1 / p.toReal)) *
          ∑ n ∈ Finset.Ioc ((i : ℤ) - r) i, eLpNorm g p (volume.restrict (dyadicIco k n.toNat))
            := by
        ring
    _ = _ := by rw [h1, mul_one]

end Interval
