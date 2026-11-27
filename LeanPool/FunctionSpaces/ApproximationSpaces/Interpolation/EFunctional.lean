/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Interpolation.Couple

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The E-functional of a couple and the approximation spaces `E_{α,q}`

For a couple `A = (N₀, N₁)` on an abelian group `U` (`InterpCouple`), with `N₀` the ambient
quasi-norm and `N₁` a measure of complexity, the **E-functional** is the error of best
approximation by elements of complexity at most `t`,

`E(t, u) = inf {N₀(u - b) : N₁(b) ≤ t}`   (`InterpCouple.eFunctional`),

as in Bergh–Löfström, Section 7.1. Bergh–Löfström put the complexity first: their
`E(t, a; A₀, A₁)` is `eFunctional` of the swapped couple. The E-functional decreases in `t`,
and for a subadditive complexity with `N₁(0) = 0` it satisfies
`E(t + s, u + v) ≤ C (E(t, u) + E(s, v))` when `N₀` satisfies the quasi-triangle inequality with
a finite constant `C` (Bergh–Löfström, Lemma 7.1.1;
`InterpCouple.eFunctional_add_le`), and `E(t + s, u + v)^ρ ≤ E(t, u)^ρ + E(s, v)^ρ` when `N₀^ρ`
is subadditive (`InterpCouple.eFunctional_add_rpow_le`). No triangle inequality and no
homogeneity is needed, so the couple may consist of quasi-norms such as `‖·‖_p` for `p < 1`.

The **approximation space** `E_{α,q}` consists of the `u` with
`‖u‖_{α,q;E} = Φ_{-α,q}(E(·, u)) = (∫_0^∞ (t^α E(t, u))^q dt/t)^(1/q) < ∞`
(`InterpCouple.eMethodNorm`, `InterpCouple.MemEMethod`). Bergh–Löfström, Definition 7.1.5,
uses compatible quasi-normed couples, with `α > 0` and `q > 0` or with `α ≥ 0` and `q = ∞`.
The definitions here also use the `eLpNorm` convention for `q = 0`.
The dyadic form is `N₀(u) + ‖(2^(kα) E(2^k, u))_k‖_{ℓ_q}` (`InterpCouple.eNormDyadic`). When
`N₁(0) = 0` and only `0` has complexity below `1`, the two give the same space for `α > 0` and
`q ≠ 0`, and for `α = 0` and `q = ∞`, with explicit constants
(`InterpCouple.memEMethod_iff_eNormDyadic_lt_top`); the comparison holds for every decreasing
function in place of `E(·, u)` (`ApproximationScheme.phiFunctional_neg_le_of_antitone`,
`ApproximationScheme.lqNorm_le_phiFunctional_neg_of_antitone`). The dyadic norm satisfies a
quasi-triangle inequality (`InterpCouple.eNormDyadic_add_le`), the counterpart with the added
ambient norm of the continuous estimate in Bergh–Löfström, Lemma 7.1.6.

The **complexity couple** of a sequence of sets `S n` is `(N, min {n : b ∈ S n})`
(`InterpCouple.complexity`); for increasing sets its E-functional at `t = n` is the error of best
approximation from `S n` (`InterpCouple.eFunctional_complexity_natCast`). The couple
`InterpCouple.ofMonotoneSubgroups` puts an increasing sequence of subgroups `V_j` at the
complexities `2^j`. For an approximation scheme in a normed space the complexity couple
(`ApproximationScheme.complexityCouple`) has `E(n, f) = E_n(f)`, and `E_{s,q}` is the
approximation space `A^s_q` for `s > 0` and `q ≠ 0`, and for `s = 0` and `q = ∞`
(`ApproximationScheme.memEMethod_complexityCouple_iff`). The couple needs only an abelian group,
so quasi-normed spaces such as `L_p`, `0 < p < 1`, have approximation spaces of this form.
-/

@[expose] public section

open MeasureTheory Set Function
open scoped ENNReal Pointwise
open ENNReal (lqNorm dyadicWeight LpAddConst dyadicGeomConst)

namespace ApproximationScheme

/-! ### The functional `Φ_{-α,q}` of a decreasing function -/

variable {α : ℝ} {q : ℝ≥0∞} {φ : ℝ≥0∞ → ℝ≥0∞}

/-- **Upper bound on a piece for a decreasing function**: for a decreasing `φ`, `α ≥ 0` and
`t ∈ [2^n, 2^(n+1))`, `t^α φ(t) ≤ 2^((n+1)α) φ(2^n)`. -/
theorem phiIntegrand_neg_le_of_antitone (hφ : Antitone φ) (hα : 0 ≤ α) {n : ℤ} {t : ℝ}
    (ht : t ∈ dyadicPiece 1 n) :
    phiIntegrand (-α) φ t ≤ 2 ^ (((n + 1 : ℤ) : ℝ) * α) * φ (2 ^ (n : ℝ)) := by
  have h := ofReal_mem_Icc_of_mem_dyadicPiece ht
  simp only [mul_one] at h
  rw [phiIntegrand, neg_neg, ENNReal.rpow_mul]
  exact mul_le_mul' (ENNReal.rpow_le_rpow h.2 hα) (hφ h.1)

/-- **Lower bound on a piece for a decreasing function**: for a decreasing `φ`, `α ≥ 0` and
`t ∈ [2^n, 2^(n+1))`, `2^(nα) φ(2^(n+1)) ≤ t^α φ(t)`. -/
theorem le_phiIntegrand_neg_of_antitone (hφ : Antitone φ) (hα : 0 ≤ α) {n : ℤ} {t : ℝ}
    (ht : t ∈ dyadicPiece 1 n) :
    2 ^ ((n : ℝ) * α) * φ (2 ^ (((n + 1 : ℤ) : ℝ))) ≤ phiIntegrand (-α) φ t := by
  have h := ofReal_mem_Icc_of_mem_dyadicPiece ht
  simp only [mul_one] at h
  rw [phiIntegrand, neg_neg, ENNReal.rpow_mul]
  exact mul_le_mul' (ENNReal.rpow_le_rpow h.1 hα) (hφ h.2)

/-- **The functional `Φ_{-α,q}` of a decreasing function by its dyadic samples**: for a
decreasing `φ ≤ M` and `α ≥ 0`,
`Φ_{-α,q}(φ) ≤ (log 2)^(1/q) C_q (2^α ‖(2^(kα) φ(2^k))_k‖_{ℓ_q} + M γ_{α,q})`, with Mathlib's
constant `C_q = LpAddConst q` and `γ_{α,q} = dyadicGeomConst α q`. On `[2^k, 2^(k+1))` the
integrand `t^α φ(t)` is at most `2^α 2^(kα) φ(2^k)`, and on `[2^(-k-1), 2^(-k))` at most
`2^(-kα) M`. -/
theorem phiFunctional_neg_le_of_antitone (hφ : Antitone φ) (hα : 0 ≤ α) {M : ℝ≥0∞}
    (hM : ∀ t, φ t ≤ M) :
    phiFunctional (-α) q φ ≤ ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal) * (LpAddConst q *
      (2 ^ α * lqNorm q (fun k : ℕ => dyadicWeight α k * φ ((2 ^ k : ℕ) : ℝ≥0∞)) +
        M * dyadicGeomConst α q)) := by
  set a : ℕ → ℝ≥0∞ := fun k => 2 ^ α * (dyadicWeight α k * φ ((2 ^ k : ℕ) : ℝ≥0∞)) with ha
  set b : ℕ → ℝ≥0∞ := fun k => M * dyadicWeight (-α) k with hb
  have hneg : Injective Int.negSucc := fun _ _ h => Int.negSucc.inj h
  have hnat : ∀ k : ℕ, ∀ t ∈ dyadicPiece 1 k, phiIntegrand (-α) φ t ≤ a k := by
    intro k t ht
    refine (phiIntegrand_neg_le_of_antitone hφ hα ht).trans (le_of_eq ?_)
    have e1 : (2 : ℝ≥0∞) ^ ((((k : ℤ) + 1 : ℤ) : ℝ) * α) = 2 ^ α * dyadicWeight α k := by
      rw [dyadicWeight, ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
      congr 1
      push_cast
      ring
    rw [e1, ENNReal.two_rpow_intCast_natCast, mul_assoc, ha]
  have hnegs : ∀ k : ℕ, ∀ t ∈ dyadicPiece 1 (Int.negSucc k), phiIntegrand (-α) φ t ≤ b k := by
    intro k t ht
    refine (phiIntegrand_neg_le_of_antitone hφ hα ht).trans ?_
    have e2 : (2 : ℝ≥0∞) ^ (((Int.negSucc k + 1 : ℤ) : ℝ) * α) = dyadicWeight (-α) k := by
      rw [dyadicWeight]
      congr 1
      rw [Int.cast_add, Int.cast_negSucc]
      push_cast
      ring
    rw [e2]
    exact (mul_le_mul' le_rfl (hM _)).trans_eq (mul_comm _ _)
  have hpiece : ∀ n : ℤ, ∀ t ∈ dyadicPiece 1 n, phiIntegrand (-α) φ t ≤
      extend (Nat.cast : ℕ → ℤ) a 0 n + extend Int.negSucc b 0 n := by
    intro n t ht
    cases n with
    | ofNat k =>
      rw [Int.ofNat_eq_natCast] at ht ⊢
      rw [Nat.cast_injective.extend_apply]
      exact le_add_right (hnat k t ht)
    | negSucc k =>
      rw [hneg.extend_apply]
      exact le_add_left (hnegs k t ht)
  have hμ : ∀ n, kMethodMeasure (dyadicPiece 1 n) = ENNReal.ofReal (Real.log 2) := fun n => by
    rw [kMethodMeasure_dyadicPiece zero_le_one, one_mul]
  calc phiFunctional (-α) q φ = eLpNorm (phiIntegrand (-α) φ) q kMethodMeasure := rfl
    _ ≤ ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal) *
          lqNorm q (fun n => extend (Nat.cast : ℕ → ℤ) a 0 n + extend Int.negSucc b 0 n) :=
        eLpNorm_le_of_le_on_pieces
          (measurable_phiIntegrand_of_measurable hφ.measurable).aestronglyMeasurable
          (measurableSet_dyadicPiece 1) (pairwise_disjoint_dyadicPiece zero_le_one)
          (ae_mem_iUnion_dyadicPiece one_pos) hμ hpiece
    _ ≤ ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal) * (LpAddConst q *
          (lqNorm q (extend (Nat.cast : ℕ → ℤ) a 0) + lqNorm q (extend Int.negSucc b 0))) := by
        gcongr
        exact ENNReal.lqNorm_add_le' q _ _
    _ ≤ _ := by
        rw [ENNReal.lqNorm_extend_zero Nat.cast_injective, ENNReal.lqNorm_extend_zero hneg, ha,
          hb, ENNReal.lqNorm_const_mul, ENNReal.lqNorm_const_mul]
        gcongr
        exact ENNReal.lqNorm_dyadicWeight_neg_le_dyadicGeomConst hα

/-- **A lower bound on the shifted dyadic pieces bounds `Φ_{θ,q}` below**: if
`a_k ≤ t^(-θ) φ(t)` for every `k ∈ ℕ` and every `t ∈ [2^(k-1), 2^k)`, then
`(log 2)^(1/q) ‖a‖_{ℓ_q} ≤ Φ_{θ,q}(φ)`. The pieces are disjoint, each of measure `log 2` for
`dt/t`. -/
theorem le_phiFunctional_of_le_on_shifted_pieces {θ : ℝ} {a : ℕ → ℝ≥0∞}
    (h : ∀ k : ℕ, ∀ t ∈ dyadicPiece 1 ((k : ℤ) - 1), a k ≤ phiIntegrand θ φ t) :
    ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal) * lqNorm q a ≤ phiFunctional θ q φ := by
  have hinj : Injective fun k : ℕ => (k : ℤ) - 1 := fun i j h => by simpa using h
  have hc : ENNReal.ofReal (Real.log 2) ≠ 0 := by
    rw [← one_mul (Real.log 2)]
    exact ofReal_mul_log_two_ne_zero one_pos
  rw [phiFunctional_eq]
  exact le_eLpNorm_of_le_on_pieces (S := fun k : ℕ => dyadicPiece 1 ((k : ℤ) - 1))
    (fun k => measurableSet_dyadicPiece 1 _)
    ((pairwise_disjoint_dyadicPiece zero_le_one).comp_of_injective hinj)
    (fun k => by rw [kMethodMeasure_dyadicPiece zero_le_one, one_mul]) hc h

/-- **The dyadic samples of a decreasing function by `Φ_{-α,q}`**: for a decreasing `φ` and
`α ≥ 0`, `(log 2)^(1/q) 2^(-α) ‖(2^(kα) φ(2^k))_k‖_{ℓ_q} ≤ Φ_{-α,q}(φ)`, since
`t^α φ(t) ≥ 2^(-α) 2^(kα) φ(2^k)` on `[2^(k-1), 2^k)`. -/
theorem lqNorm_le_phiFunctional_neg_of_antitone (hφ : Antitone φ) (hα : 0 ≤ α) :
    ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal) *
      (2 ^ (-α) * lqNorm q (fun k : ℕ => dyadicWeight α k * φ ((2 ^ k : ℕ) : ℝ≥0∞))) ≤
        phiFunctional (-α) q φ := by
  rw [← ENNReal.lqNorm_const_mul]
  refine le_phiFunctional_of_le_on_shifted_pieces fun k t ht => ?_
  refine le_trans (le_of_eq ?_) (le_phiIntegrand_neg_of_antitone hφ hα ht)
  have e1 : ((((k : ℤ) - 1 + 1 : ℤ)) : ℝ) = ((k : ℤ) : ℝ) := by rw [sub_add_cancel]
  have e2 : (2 : ℝ≥0∞) ^ ((((k : ℤ) - 1 : ℤ) : ℝ) * α) = 2 ^ (-α) * dyadicWeight α k := by
    rw [dyadicWeight, ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
    congr 1
    push_cast
    ring
  rw [e1, e2, ENNReal.two_rpow_intCast_natCast, mul_assoc]

/-- **A lower bound of `φ` near `0` bounds `Φ_{-α,q}` below**: if `M ≤ φ(t)` for every `t < 1`,
`α ≥ 0` and `q ≠ 0`, then `(log 2)^(1/q) 2^(-α) M ≤ Φ_{-α,q}(φ)`, from the piece `[1/2, 1)`. -/
theorem le_phiFunctional_neg_of_le (hα : 0 ≤ α) (hq0 : q ≠ 0) {M : ℝ≥0∞}
    (hM : ∀ t < 1, M ≤ φ t) :
    ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal) * (2 ^ (-α) * M) ≤ phiFunctional (-α) q φ := by
  rw [← ENNReal.lqNorm_ite_eq hq0 0 (2 ^ (-α) * M)]
  refine le_phiFunctional_of_le_on_shifted_pieces fun k t ht => ?_
  split_ifs with hk
  · subst hk
    have hpiece : dyadicPiece 1 (((0 : ℕ) : ℤ) - 1) = Ico (2⁻¹ : ℝ) 1 := by
      norm_num [dyadicPiece]
    rw [hpiece] at ht
    rw [phiIntegrand, neg_neg]
    refine mul_le_mul' ?_ (hM _ (ENNReal.ofReal_lt_one.2 ht.2))
    calc (2 : ℝ≥0∞) ^ (-α) = ENNReal.ofReal 2⁻¹ ^ α := by
          rw [ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat, ENNReal.inv_rpow,
            ENNReal.rpow_neg]
      _ ≤ ENNReal.ofReal t ^ α := ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal ht.1) hα
  · exact zero_le

end ApproximationScheme

namespace InterpCouple

variable {U : Type*} [AddCommGroup U]

/-! ### The E-functional -/

/-- The **E-functional** of a couple `A = (N₀, N₁)`: the error of best approximation of `u` in
`N₀` by elements of complexity `N₁(b) ≤ t`, `E(t, u) = inf {N₀(u - b) : N₁(b) ≤ t}`, with the
value `∞` if no `b` has `N₁(b) ≤ t` (Bergh–Löfström, Section 7.1). Bergh–Löfström put the
complexity first: their `E(t, a; A₀, A₁)` is `eFunctional` of the swapped couple
`(‖·‖_{A₁}, ‖·‖_{A₀})`. -/
noncomputable def eFunctional (A : InterpCouple U) (t : ℝ≥0∞) (u : U) : ℝ≥0∞ :=
  ⨅ b : {b : U // A.norm1 b ≤ t}, A.norm0 (u - b)

variable {A : InterpCouple U} {t s C : ℝ≥0∞} {ρ : ℝ}

/-- Every admissible element bounds the E-functional: `E(t, u) ≤ N₀(u - b)` if `N₁(b) ≤ t`. -/
theorem eFunctional_le {b u : U} (hb : A.norm1 b ≤ t) : A.eFunctional t u ≤ A.norm0 (u - b) :=
  iInf_le_of_le ⟨b, hb⟩ le_rfl

/-- A lower bound of `N₀(u - b)` for every admissible `b` is a lower bound of `E(t, u)`. -/
theorem le_eFunctional {F : ℝ≥0∞} {u : U} (h : ∀ b, A.norm1 b ≤ t → F ≤ A.norm0 (u - b)) :
    F ≤ A.eFunctional t u :=
  le_iInf fun b => h b b.2

/-- **The E-functional decreases in `t`** (Bergh–Löfström, Lemma 7.1.1): more elements are
admissible for a larger `t`. -/
theorem eFunctional_anti (u : U) : Antitone fun t => A.eFunctional t u :=
  fun _ _ h => le_eFunctional fun _ hb => eFunctional_le (hb.trans h)

/-- `E(t, u) ≤ N₀(u)` if `N₁(0) = 0`, from `b = 0`. -/
theorem eFunctional_le_norm0 (h1 : A.norm1 0 = 0) (u : U) : A.eFunctional t u ≤ A.norm0 u :=
  (eFunctional_le (by rw [h1]; exact zero_le)).trans_eq (by rw [sub_zero])

/-- `E(t, 0) = 0` if both norms vanish at `0`. -/
theorem eFunctional_zero_right (h0 : A.norm0 0 = 0) (h1 : A.norm1 0 = 0) :
    A.eFunctional t 0 = 0 :=
  le_antisymm ((eFunctional_le_norm0 h1 0).trans_eq h0) bot_le

/-- **If every `b` with `N₁(b) < 1` is `0`, then `E(t, u) ≥ N₀(u)` for `t < 1`**: every
admissible element is `b = 0`. -/
theorem norm0_le_eFunctional_of_lt_one (hdisc : ∀ b, A.norm1 b < 1 → b = 0) (ht : t < 1)
    (u : U) : A.norm0 u ≤ A.eFunctional t u :=
  le_eFunctional fun b hb => le_of_eq (by rw [hdisc b (hb.trans_lt ht), sub_zero])

/-- The E-functional of a couple of even functions is even: `E(t, -u) = E(t, u)`, by the
substitution `b ↦ -b`. -/
theorem eFunctional_neg (h0 : ∀ a, A.norm0 (-a) = A.norm0 a) (h1 : ∀ a, A.norm1 (-a) = A.norm1 a)
    (u : U) : A.eFunctional t (-u) = A.eFunctional t u := by
  have key : ∀ v, A.eFunctional t (-v) ≤ A.eFunctional t v := fun v =>
    le_eFunctional fun b hb => (eFunctional_le (b := -b) (by rwa [h1])).trans_eq
      (by rw [← h0, show -(-v - -b) = v - b by abel])
  exact le_antisymm (key u) (by simpa using key (-u))

/-- **Near-best elements**: if `E(t, u) < ∞` and `ε > 0`, some `b` with `N₁(b) ≤ t` has
`N₀(u - b) ≤ E(t, u) + ε`. -/
theorem exists_norm0_sub_le_eFunctional_add {u : U} {ε : ℝ≥0∞} (h : A.eFunctional t u ≠ ∞)
    (hε : ε ≠ 0) : ∃ b, A.norm1 b ≤ t ∧ A.norm0 (u - b) ≤ A.eFunctional t u + ε := by
  obtain ⟨b, hb⟩ := iInf_lt_iff.1 (ENNReal.lt_add_right h hε)
  exact ⟨b, b.2, hb.le⟩

/-- The decomposition bound behind the subadditivity of the E-functional: if `N₀` satisfies the
quasi-triangle inequality with constant `C`, `N₁` is subadditive, `N₁(b) ≤ t` and `N₁(b') ≤ s`,
then `E(t + s, u + v) ≤ C (N₀(u - b) + N₀(v - b'))`. -/
theorem eFunctional_add_le_of_le (h0 : ∀ a b, A.norm0 (a + b) ≤ C * (A.norm0 a + A.norm0 b))
    (h1 : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b) {u v b b' : U} (hb : A.norm1 b ≤ t)
    (hb' : A.norm1 b' ≤ s) :
    A.eFunctional (t + s) (u + v) ≤ C * (A.norm0 (u - b) + A.norm0 (v - b')) :=
  (eFunctional_le ((h1 b b').trans (add_le_add hb hb'))).trans
    ((le_of_eq (by rw [add_sub_add_comm])).trans (h0 _ _))

/-- **Subadditivity of the E-functional** (Bergh–Löfström, Lemma 7.1.1, with `c₀ = 1`): if `N₀`
satisfies the quasi-triangle inequality with a finite constant `C`, `N₁(0) = 0` and `N₁` is
subadditive, then `E(t + s, u + v) ≤ C (E(t, u) + E(s, v))`. The hypothesis `N₁(0) = 0` serves
the case `C = 0`, in which `N₀` vanishes and the left side is `0` once `b = 0` is admissible. -/
theorem eFunctional_add_le (hC : C ≠ ∞) (h10 : A.norm1 0 = 0)
    (h0 : ∀ a b, A.norm0 (a + b) ≤ C * (A.norm0 a + A.norm0 b))
    (h1 : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b) (t s : ℝ≥0∞) (u v : U) :
    A.eFunctional (t + s) (u + v) ≤ C * (A.eFunctional t u + A.eFunctional s v) := by
  rcases eq_or_ne C 0 with rfl | hC0
  · refine (eFunctional_le_norm0 h10 _).trans ?_
    simpa using h0 u v
  have hu : C * A.eFunctional t u = ⨅ b : {b : U // A.norm1 b ≤ t}, C * A.norm0 (u - b) :=
    ENNReal.mul_iInf_of_ne hC0 hC
  have hv : C * A.eFunctional s v = ⨅ b : {b : U // A.norm1 b ≤ s}, C * A.norm0 (v - b) :=
    ENNReal.mul_iInf_of_ne hC0 hC
  rw [mul_add, hu, hv]
  exact ENNReal.le_iInf_add_iInf fun b b' =>
    (eFunctional_add_le_of_le h0 h1 b.2 b'.2).trans_eq (mul_add _ _ _)

/-- **`ρ`-subadditivity of the E-functional**: if `N₀^ρ` is subadditive for some `ρ > 0` and
`N₁` is subadditive, then `E(t + s, u + v)^ρ ≤ E(t, u)^ρ + E(s, v)^ρ`. The power `x ↦ x^ρ` is an
order isomorphism of `[0, ∞]`, so `E(t, u)^ρ` is the infimum of the `N₀(u - b)^ρ`. -/
theorem eFunctional_add_rpow_le (hρ : 0 < ρ)
    (h0 : ∀ a b, A.norm0 (a + b) ^ ρ ≤ A.norm0 a ^ ρ + A.norm0 b ^ ρ)
    (h1 : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b) (t s : ℝ≥0∞) (u v : U) :
    A.eFunctional (t + s) (u + v) ^ ρ ≤ A.eFunctional t u ^ ρ + A.eFunctional s v ^ ρ := by
  have hu : A.eFunctional t u ^ ρ = ⨅ b : {b : U // A.norm1 b ≤ t}, A.norm0 (u - b) ^ ρ :=
    (ENNReal.orderIsoRpow ρ hρ).map_iInf _
  have hv : A.eFunctional s v ^ ρ = ⨅ b : {b : U // A.norm1 b ≤ s}, A.norm0 (v - b) ^ ρ :=
    (ENNReal.orderIsoRpow ρ hρ).map_iInf _
  rw [hu, hv]
  refine ENNReal.le_iInf_add_iInf fun b b' => ?_
  calc A.eFunctional (t + s) (u + v) ^ ρ ≤ A.norm0 ((u - b) + (v - b')) ^ ρ := by
        refine ENNReal.rpow_le_rpow ?_ hρ.le
        rw [← add_sub_add_comm]
        exact eFunctional_le ((h1 _ _).trans (add_le_add b.2 b'.2))
    _ ≤ _ := h0 _ _

/-! ### The spaces `E_{α,q}` -/

/-- The norm of the **approximation space** `E_{α,q}` of the couple extends the formula
in Bergh–Löfström, Definition 7.1.5, to all real `α` and includes the case `q = 0`.
It is `‖u‖_{α,q;E} = Φ_{-α,q}(E(·, u))`, that is
`(∫_0^∞ (t^α E(t, u))^q dt/t)^(1/q)` for `0 < q < ∞` and the essential supremum of
`t^α E(t, u)` for `q = ∞`, and `0` for `q = 0`. -/
noncomputable def eMethodNorm (A : InterpCouple U) (α : ℝ) (q : ℝ≥0∞) (u : U) : ℝ≥0∞ :=
  ApproximationScheme.phiFunctional (-α) q fun t => A.eFunctional t u

/-- `u` belongs to the **approximation space** `E_{α,q}` of the couple: `‖u‖_{α,q;E} < ∞`. -/
def MemEMethod (A : InterpCouple U) (α : ℝ) (q : ℝ≥0∞) (u : U) : Prop :=
  A.eMethodNorm α q u < ∞

/-- The **dyadic norm** of `E_{s,q}`: `N₀(u) + ‖(2^(ks) E(2^k, u))_{k ∈ ℕ}‖_{ℓ_q}`. For the
complexity couple of an approximation scheme it is the dyadic quasi-norm of `A^s_q`. -/
noncomputable def eNormDyadic (A : InterpCouple U) (s : ℝ) (q : ℝ≥0∞) (u : U) : ℝ≥0∞ :=
  A.norm0 u + lqNorm q fun k : ℕ => dyadicWeight s k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u

/-- The constant `(log 2)^(1/q) C_q (2^α + γ_{α,q})` of the bound of `‖·‖_{α,q;E}` by the dyadic
norm, with `C_q = LpAddConst q` and `γ_{α,q} = dyadicGeomConst α q`. -/
noncomputable def eDyadicUpperConst (α : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal) * LpAddConst q * (2 ^ α + dyadicGeomConst α q)

/-- The constant `eDyadicUpperConst α q` is finite for `α > 0`, and for every `α` if `q = ∞`
(then `γ_{α,∞} = 1`). -/
theorem eDyadicUpperConst_ne_top {α : ℝ} {q : ℝ≥0∞} (hαq : 0 < α ∨ q = ∞) :
    eDyadicUpperConst α q ≠ ∞ := by
  have hγ : dyadicGeomConst α q ≠ ∞ := by
    rcases hαq with hα | rfl
    · exact ENNReal.dyadicGeomConst_ne_top hα q
    · rw [ENNReal.dyadicGeomConst_top]
      exact ENNReal.one_ne_top
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
    (ENNReal.LpAddConst_lt_top q).ne)
    (ENNReal.add_ne_top.2 ⟨ENNReal.two_rpow_ne_top α, hγ⟩)

/-- The constant `2 · 2^α (log 2)^(-1/q)` of the bound of the dyadic norm by `‖·‖_{α,q;E}`. -/
noncomputable def eDyadicLowerConst (α : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ :=
  2 * 2 ^ α * (ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal))⁻¹

/-- The constant `eDyadicLowerConst α q` is finite. -/
theorem eDyadicLowerConst_ne_top (α : ℝ) (q : ℝ≥0∞) : eDyadicLowerConst α q ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.two_rpow_ne_top α))
    (ENNReal.inv_ne_top.2 (ApproximationScheme.ofReal_log_two_rpow_ne_zero q))

variable {α : ℝ} {q : ℝ≥0∞}

/-- **The norm of `E_{α,q}` by the dyadic norm**: if `N₁(0) = 0` and `α ≥ 0`, then
`‖u‖_{α,q;E} ≤ eDyadicUpperConst α q · (N₀(u) + ‖(2^(kα) E(2^k, u))_k‖_{ℓ_q})`; the constant is
finite for `α > 0` and for `q = ∞`. -/
theorem eMethodNorm_le_eNormDyadic (h1 : A.norm1 0 = 0) (hα : 0 ≤ α) (u : U) :
    A.eMethodNorm α q u ≤ eDyadicUpperConst α q * A.eNormDyadic α q u := by
  set L := lqNorm q fun k : ℕ => dyadicWeight α k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u
  set γ := dyadicGeomConst α q
  set X := ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal)
  calc A.eMethodNorm α q u ≤ X * (LpAddConst q * (2 ^ α * L + A.norm0 u * γ)) :=
        ApproximationScheme.phiFunctional_neg_le_of_antitone (eFunctional_anti u) hα
          fun _ => eFunctional_le_norm0 h1 u
    _ ≤ X * (LpAddConst q * ((2 ^ α + γ) * L + A.norm0 u * (2 ^ α + γ))) := by
        gcongr
        · exact le_self_add
        · exact le_add_self
    _ = X * LpAddConst q * (2 ^ α + γ) * (A.norm0 u + L) := by ring
    _ = eDyadicUpperConst α q * A.eNormDyadic α q u := rfl

/-- **The dyadic norm by the norm of `E_{α,q}`**: if every `b` with `N₁(b) < 1` is `0`,
`α ≥ 0` and `q ≠ 0`, then
`N₀(u) + ‖(2^(kα) E(2^k, u))_k‖_{ℓ_q} ≤ eDyadicLowerConst α q · ‖u‖_{α,q;E}`. On `(0, 1)` the
E-functional is at least `N₀(u)`, which bounds the first term. -/
theorem eNormDyadic_le_eMethodNorm (hdisc : ∀ b, A.norm1 b < 1 → b = 0) (hα : 0 ≤ α)
    (hq0 : q ≠ 0) (u : U) :
    A.eNormDyadic α q u ≤ eDyadicLowerConst α q * A.eMethodNorm α q u := by
  have hX0 := ApproximationScheme.ofReal_log_two_rpow_ne_zero q
  have hXt : ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have h20 : (2 : ℝ≥0∞) ^ (-α) ≠ 0 := (ENNReal.rpow_pos two_pos ENNReal.ofNat_ne_top).ne'
  have hc0 := mul_ne_zero hX0 h20
  have hct := ENNReal.mul_ne_top hXt (ENNReal.two_rpow_ne_top (-α))
  have hN : ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal) * 2 ^ (-α) * A.norm0 u ≤
      A.eMethodNorm α q u := by
    rw [mul_assoc]
    exact ApproximationScheme.le_phiFunctional_neg_of_le (φ := fun t => A.eFunctional t u) hα
      hq0 fun t ht => norm0_le_eFunctional_of_lt_one hdisc ht u
  have hL : ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal) * 2 ^ (-α) *
      lqNorm q (fun k : ℕ => dyadicWeight α k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u) ≤
        A.eMethodNorm α q u := by
    rw [mul_assoc]
    exact ApproximationScheme.lqNorm_le_phiFunctional_neg_of_antitone
      (φ := fun t => A.eFunctional t u) (eFunctional_anti u) hα
  rw [ENNReal.mul_le_iff_le_inv hc0 hct] at hN hL
  have hinv : (ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal) * 2 ^ (-α))⁻¹ =
      2 ^ α * (ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal))⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl hX0) (Or.inr h20), ENNReal.rpow_neg, inv_inv, mul_comm]
  rw [hinv] at hN hL
  calc A.eNormDyadic α q u ≤ 2 ^ α * (ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal))⁻¹ *
        A.eMethodNorm α q u + 2 ^ α * (ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal))⁻¹ *
          A.eMethodNorm α q u := add_le_add hN hL
    _ = eDyadicLowerConst α q * A.eMethodNorm α q u := by
        rw [eDyadicLowerConst]
        ring

/-- **The space `E_{α,q}` by its dyadic norm**: if `N₁(0) = 0` and only `0` has complexity
below `1`, then for `α ≥ 0` and `q ≠ 0` with `α > 0` or `q = ∞` (the range of Bergh–Löfström,
Definition 7.1.5), `u ∈ E_{α,q}` iff `N₀(u) + ‖(2^(kα) E(2^k, u))_k‖_{ℓ_q} < ∞`. -/
theorem memEMethod_iff_eNormDyadic_lt_top (h1 : A.norm1 0 = 0)
    (hdisc : ∀ b, A.norm1 b < 1 → b = 0) (hα : 0 ≤ α) (hαq : 0 < α ∨ q = ∞) (hq0 : q ≠ 0)
    {u : U} : A.MemEMethod α q u ↔ A.eNormDyadic α q u < ∞ :=
  ⟨fun h => (eNormDyadic_le_eMethodNorm hdisc hα hq0 u).trans_lt
      (ENNReal.mul_lt_top (eDyadicLowerConst_ne_top α q).lt_top h),
    fun h => (eMethodNorm_le_eNormDyadic h1 hα u).trans_lt
      (ENNReal.mul_lt_top (eDyadicUpperConst_ne_top hαq).lt_top h)⟩

/-- The constant `C C_q (2 + 2^s C_q)` of the quasi-triangle inequality of the dyadic norm, for a
couple quasi-normed with constant `C` and Mathlib's constant `C_q = LpAddConst q`. -/
noncomputable def eAddConst (C : ℝ≥0∞) (s : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ :=
  C * LpAddConst q * (2 + 2 ^ s * LpAddConst q)

/-- The constant `eAddConst C s q` is finite for `C < ∞`. -/
theorem eAddConst_ne_top (hC : C ≠ ∞) (s : ℝ) (q : ℝ≥0∞) : eAddConst C s q ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top hC (ENNReal.LpAddConst_lt_top q).ne)
    (ENNReal.add_ne_top.2 ⟨ENNReal.ofNat_ne_top,
      ENNReal.mul_ne_top (ENNReal.two_rpow_ne_top s) (ENNReal.LpAddConst_lt_top q).ne⟩)

/-- One level up: `2^((k+1)s) E(2^(k+1), u + v) ≤ 2^s C (2^(ks) E(2^k, u) + 2^(ks) E(2^k, v))`
for a couple quasi-normed with constant `C` with subadditive complexity, since
`2^(k+1) = 2^k + 2^k` (`eFunctional_add_le`). -/
theorem dyadicWeight_succ_mul_eFunctional_add_le (hA : A.IsQuasiNormed C)
    (h1 : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b) (s : ℝ) (u v : U) (k : ℕ) :
    dyadicWeight s (k + 1) * A.eFunctional ((2 ^ (k + 1) : ℕ) : ℝ≥0∞) (u + v) ≤
      2 ^ s * C * (dyadicWeight s k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u +
        dyadicWeight s k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) v) := by
  have h2 : ((2 ^ (k + 1) : ℕ) : ℝ≥0∞) = ((2 ^ k : ℕ) : ℝ≥0∞) + ((2 ^ k : ℕ) : ℝ≥0∞) := by
    push_cast
    ring
  rw [h2, ENNReal.dyadicWeight_succ]
  calc 2 ^ s * dyadicWeight s k * A.eFunctional (((2 ^ k : ℕ) : ℝ≥0∞) + ((2 ^ k : ℕ) : ℝ≥0∞))
        (u + v) ≤ 2 ^ s * dyadicWeight s k * (C * (A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u +
          A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) v)) := by
        gcongr
        exact eFunctional_add_le hA.ne_top hA.norm1_zero hA.norm0_add_le h1 _ _ u v
    _ = _ := by ring

/-- **The quasi-triangle inequality of the dyadic norm**. This is the dyadic estimate with the
added ambient norm, analogous to the continuous estimate in Bergh–Löfström, Lemma 7.1.6.
For a couple quasi-normed with constant `C` whose complexity is subadditive,
`‖u + v‖ ≤ C C_q (2 + 2^s C_q) (‖u‖ + ‖v‖)` for the norm `N₀(u) + ‖(2^(ks) E(2^k, u))_k‖_{ℓ_q}`,
by `E(2^(k+1), u + v) ≤ C (E(2^k, u) + E(2^k, v))` and the shift by one level. -/
theorem eNormDyadic_add_le (hA : A.IsQuasiNormed C)
    (h1 : ∀ a b, A.norm1 (a + b) ≤ A.norm1 a + A.norm1 b) (s : ℝ) (q : ℝ≥0∞) (u v : U) :
    A.eNormDyadic s q (u + v) ≤ eAddConst C s q * (A.eNormDyadic s q u + A.eNormDyadic s q v) := by
  set x : ℕ → ℝ≥0∞ := fun k => dyadicWeight s k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) (u + v)
  set yu : ℕ → ℝ≥0∞ := fun k => dyadicWeight s k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) u
  set yv : ℕ → ℝ≥0∞ := fun k => dyadicWeight s k * A.eFunctional ((2 ^ k : ℕ) : ℝ≥0∞) v
  set Cq := LpAddConst q
  have hP : A.norm0 (u + v) ≤ C * (A.norm0 u + A.norm0 v) := hA.norm0_add_le u v
  have hx0 : x 0 ≤ C * (A.norm0 u + A.norm0 v) := by
    simp only [x, ENNReal.dyadicWeight_zero_right, one_mul]
    exact (eFunctional_le_norm0 hA.norm1_zero _).trans hP
  have hshift : lqNorm q (fun k => x (k + 1)) ≤ 2 ^ s * C * (Cq * (lqNorm q yu + lqNorm q yv)) := by
    calc lqNorm q (fun k => x (k + 1)) ≤ lqNorm q (fun k => 2 ^ s * C * (yu k + yv k)) :=
          ENNReal.lqNorm_mono fun k => dyadicWeight_succ_mul_eFunctional_add_le hA h1 s u v k
      _ ≤ _ := by
          rw [ENNReal.lqNorm_const_mul]
          gcongr
          exact ENNReal.lqNorm_add_le' q _ _
  have hCq : 1 ≤ Cq := ENNReal.one_le_LpAddConst q
  calc A.eNormDyadic s q (u + v) = A.norm0 (u + v) + lqNorm q x := rfl
    _ ≤ Cq * (C * (A.norm0 u + A.norm0 v)) + Cq * (C * (A.norm0 u + A.norm0 v) +
          2 ^ s * C * (Cq * (lqNorm q yu + lqNorm q yv))) := by
        gcongr
        · exact hP.trans (le_mul_of_one_le_left' hCq)
        · exact (ENNReal.lqNorm_le_head_add_shift' q x).trans (by gcongr)
    _ = C * Cq * (2 * (A.norm0 u + A.norm0 v) +
          2 ^ s * Cq * (lqNorm q yu + lqNorm q yv)) := by ring
    _ ≤ C * Cq * ((2 + 2 ^ s * Cq) * (A.norm0 u + A.norm0 v) +
          (2 + 2 ^ s * Cq) * (lqNorm q yu + lqNorm q yv)) := by
        gcongr
        · exact le_self_add
        · exact le_add_self
    _ = C * Cq * (2 + 2 ^ s * Cq) * ((A.norm0 u + lqNorm q yu) + (A.norm0 v + lqNorm q yv)) := by
        ring
    _ = eAddConst C s q * (A.eNormDyadic s q u + A.eNormDyadic s q v) := rfl

/-! ### The complexity couple -/

/-- The **complexity couple** of a function `N : U → [0, ∞]` and a sequence of sets `S n`:
`N₀ = N` and `N₁(b) = min {n : b ∈ S n}`, with `N₁(b) = ∞` if `b` lies in no `S n`. -/
noncomputable def complexity (N : U → ℝ≥0∞) (S : ℕ → Set U) : InterpCouple U :=
  ⟨N, fun b => ⨅ n : {n : ℕ // b ∈ S n}, ((n : ℕ) : ℝ≥0∞)⟩

variable {N : U → ℝ≥0∞} {S : ℕ → Set U}

/-- The first norm of the complexity couple is `N`. -/
@[simp]
theorem complexity_norm0 (u : U) : (complexity N S).norm0 u = N u := rfl

/-- An element of `S n` has complexity at most `n`. -/
theorem complexity_norm1_le_of_mem {b : U} {n : ℕ} (h : b ∈ S n) :
    (complexity N S).norm1 b ≤ n :=
  iInf_le_of_le ⟨n, h⟩ le_rfl

/-- For increasing sets, an element of complexity at most `n` lies in `S n`: every `m` with
`b ∈ S m` exceeds `n` otherwise, and then the complexity is at least `n + 1`. -/
theorem mem_of_complexity_norm1_le (hS : Monotone S) {b : U} {n : ℕ}
    (h : (complexity N S).norm1 b ≤ n) : b ∈ S n := by
  by_contra hb
  have hge : (((n + 1 : ℕ)) : ℝ≥0∞) ≤ (complexity N S).norm1 b := le_iInf fun m => by
    have hm : n < m := by
      by_contra hm
      exact hb (hS (not_lt.1 hm) m.2)
    exact Nat.cast_le.2 hm
  have := Nat.cast_le.1 (hge.trans h)
  omega

/-- For increasing sets, `N₁(b) ≤ n` iff `b ∈ S n`. -/
theorem complexity_norm1_le_natCast_iff (hS : Monotone S) {b : U} {n : ℕ} :
    (complexity N S).norm1 b ≤ n ↔ b ∈ S n :=
  ⟨mem_of_complexity_norm1_le hS, complexity_norm1_le_of_mem⟩

/-- **The E-functional of the complexity couple at an integer** is the error of best
approximation from `S n`: for increasing sets, `E(n, u) = inf_{b ∈ S n} N(u - b)`. -/
theorem eFunctional_complexity_natCast (hS : Monotone S) (n : ℕ) (u : U) :
    (complexity N S).eFunctional n u = ⨅ b ∈ S n, N (u - b) :=
  le_antisymm (le_iInf₂ fun _ hb => eFunctional_le (complexity_norm1_le_of_mem hb))
    (le_eFunctional fun b hb => iInf₂_le b (mem_of_complexity_norm1_le hS hb))

/-- If `0 ∈ S 0`, the element `0` has complexity `0`. -/
theorem complexity_norm1_zero (h : (0 : U) ∈ S 0) : (complexity N S).norm1 0 = 0 :=
  nonpos_iff_eq_zero.1 ((complexity_norm1_le_of_mem h).trans_eq Nat.cast_zero)

/-- If every `S n` is symmetric, the complexity is even. -/
theorem complexity_norm1_neg (hneg : ∀ n, ∀ b ∈ S n, -b ∈ S n) (b : U) :
    (complexity N S).norm1 (-b) = (complexity N S).norm1 b := by
  have key : ∀ a : U, (complexity N S).norm1 (-a) ≤ (complexity N S).norm1 a := fun a =>
    le_iInf fun n => complexity_norm1_le_of_mem (hneg n a n.2)
  exact le_antisymm (key b) (by simpa using key (-b))

/-- If `S m + S n ⊆ S (m + n)`, the complexity is subadditive. -/
theorem complexity_norm1_add_le (hadd : ∀ m n, S m + S n ⊆ S (m + n)) (a b : U) :
    (complexity N S).norm1 (a + b) ≤ (complexity N S).norm1 a + (complexity N S).norm1 b :=
  ENNReal.le_iInf_add_iInf fun m n =>
    (complexity_norm1_le_of_mem (hadd m n (Set.add_mem_add m.2 n.2))).trans_eq (Nat.cast_add _ _)

/-- If `S 0 = {0}`, every `b` with complexity below `1` is `0`. -/
theorem eq_zero_of_complexity_norm1_lt_one (hS0 : S 0 = {0}) {b : U}
    (hb : (complexity N S).norm1 b < 1) : b = 0 := by
  obtain ⟨n, hn⟩ := iInf_lt_iff.1 hb
  have h := n.2
  rw [Nat.cast_lt_one.1 hn, hS0] at h
  exact Set.mem_singleton_iff.1 h

/-! ### Subgroups at dyadic complexities -/

/-- The **dyadic levels** of a sequence of subgroups `V_j`: `{0}` at complexity `0` and
`V_{⌊log₂ n⌋}` at complexity `n ≥ 1`, so that `V_j` sits at the complexities
`2^j, …, 2^(j+1) - 1`. -/
def dyadicLevels (V : ℕ → AddSubgroup U) (n : ℕ) : Set U :=
  if n = 0 then {0} else (V (Nat.log 2 n) : Set U)

variable {V : ℕ → AddSubgroup U}

/-- The dyadic level `0` is `{0}`. -/
theorem dyadicLevels_zero : dyadicLevels V 0 = {0} := by simp [dyadicLevels]

/-- The dyadic level `2^j` is `V_j`. -/
theorem dyadicLevels_two_pow (j : ℕ) : dyadicLevels V (2 ^ j) = V j := by
  have h : (2 ^ j : ℕ) ≠ 0 := pow_ne_zero j two_ne_zero
  simp only [dyadicLevels, h, ↓reduceIte, Nat.log_pow Nat.one_lt_two]

/-- Every dyadic level contains `0`. -/
theorem zero_mem_dyadicLevels (n : ℕ) : (0 : U) ∈ dyadicLevels V n := by
  unfold dyadicLevels
  split_ifs
  · exact Set.mem_singleton 0
  · exact SetLike.mem_coe.2 (zero_mem _)

/-- For increasing subgroups the dyadic levels increase. -/
theorem monotone_dyadicLevels (hV : Monotone V) : Monotone (dyadicLevels V) := by
  intro m n hmn b hb
  rcases eq_or_ne m 0 with rfl | hm
  · rw [dyadicLevels_zero, Set.mem_singleton_iff] at hb
    rw [hb]
    exact zero_mem_dyadicLevels n
  have hn : n ≠ 0 := by omega
  simp only [dyadicLevels, hm, hn, ↓reduceIte, SetLike.mem_coe] at hb ⊢
  exact hV (Nat.log_mono_right hmn) hb

/-- The dyadic levels are symmetric. -/
theorem neg_mem_dyadicLevels {n : ℕ} {b : U} (hb : b ∈ dyadicLevels V n) :
    -b ∈ dyadicLevels V n := by
  unfold dyadicLevels at hb ⊢
  split_ifs at hb ⊢
  · rw [Set.mem_singleton_iff] at hb ⊢
    rw [hb, neg_zero]
  · exact SetLike.mem_coe.2 (neg_mem (SetLike.mem_coe.1 hb))

/-- For increasing subgroups, `S m + S n ⊆ S (m + n)` for the dyadic levels. -/
theorem dyadicLevels_add_subset (hV : Monotone V) (m n : ℕ) :
    dyadicLevels V m + dyadicLevels V n ⊆ dyadicLevels V (m + n) := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  change a + b ∈ dyadicLevels V (m + n)
  rcases eq_or_ne m 0 with rfl | hm
  · rw [dyadicLevels_zero, Set.mem_singleton_iff] at ha
    rwa [ha, zero_add, zero_add]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [dyadicLevels_zero, Set.mem_singleton_iff] at hb
    rwa [hb, add_zero, add_zero]
  have hmn : m + n ≠ 0 := by omega
  simp only [dyadicLevels, hm, hn, hmn, ↓reduceIte, SetLike.mem_coe] at ha hb ⊢
  exact add_mem (hV (Nat.log_mono_right (by omega)) ha) (hV (Nat.log_mono_right (by omega)) hb)

/-- The **couple of an increasing sequence of subgroups** `V_0 ⊆ V_1 ⊆ ⋯` of `U` with the first
norm `N`: the complexity couple of the dyadic levels, in which `V_j` has complexity `2^j`. It
mirrors the dyadic scheme `ApproximationScheme.ofMonotoneSubmodules`, on an abelian group with a
quasi-norm in place of a normed space. As there, the proof that the subgroups increase is part
of the data, so that every couple of this form has increasing levels; the lemmas on the
subadditivity of the complexity and on the E-functional at `2^j` use it. -/
noncomputable def ofMonotoneSubgroups (N : U → ℝ≥0∞) (V : ℕ → AddSubgroup U)
    (_hV : Monotone V) : InterpCouple U :=
  complexity N (dyadicLevels V)

variable {hV : Monotone V}

/-- The first norm of the couple of subgroups is `N`. -/
@[simp]
theorem ofMonotoneSubgroups_norm0 (u : U) : (ofMonotoneSubgroups N V hV).norm0 u = N u := rfl

/-- In the couple of subgroups, `0` has complexity `0`. -/
theorem ofMonotoneSubgroups_norm1_zero : (ofMonotoneSubgroups N V hV).norm1 0 = 0 :=
  complexity_norm1_zero (zero_mem_dyadicLevels 0)

/-- In the couple of subgroups the complexity is even. -/
theorem ofMonotoneSubgroups_norm1_neg (b : U) :
    (ofMonotoneSubgroups N V hV).norm1 (-b) = (ofMonotoneSubgroups N V hV).norm1 b :=
  complexity_norm1_neg (fun _ _ hb => neg_mem_dyadicLevels hb) b

/-- In the couple of subgroups the complexity is subadditive. -/
theorem ofMonotoneSubgroups_norm1_add_le (a b : U) :
    (ofMonotoneSubgroups N V hV).norm1 (a + b) ≤
      (ofMonotoneSubgroups N V hV).norm1 a + (ofMonotoneSubgroups N V hV).norm1 b :=
  complexity_norm1_add_le (dyadicLevels_add_subset hV) a b

/-- In the couple of subgroups only `0` has complexity below `1`. -/
theorem eq_zero_of_ofMonotoneSubgroups_norm1_lt_one {b : U}
    (hb : (ofMonotoneSubgroups N V hV).norm1 b < 1) : b = 0 :=
  eq_zero_of_complexity_norm1_lt_one dyadicLevels_zero hb

/-- **The E-functional of the couple of subgroups at `t = 2^j`** is the error of best
approximation from `V_j`: `E(2^j, u) = inf_{b ∈ V_j} N(u - b)`. -/
theorem eFunctional_ofMonotoneSubgroups_two_pow (j : ℕ) (u : U) :
    (ofMonotoneSubgroups N V hV).eFunctional ((2 ^ j : ℕ) : ℝ≥0∞) u = ⨅ b ∈ V j, N (u - b) := by
  have h := eFunctional_complexity_natCast (N := N) (monotone_dyadicLevels hV) (2 ^ j) u
  rw [dyadicLevels_two_pow] at h
  exact h

/-- **The E-functional at `t = 2^j` ignores elements of `V_j`**: `E(2^j, u - a) = E(2^j, u)` for
`a ∈ V_j`, by the substitution `b ↦ a + b` of the subgroup `V_j`. -/
theorem eFunctional_ofMonotoneSubgroups_sub_of_mem {j : ℕ} {a : U} (ha : a ∈ V j) (u : U) :
    (ofMonotoneSubgroups N V hV).eFunctional ((2 ^ j : ℕ) : ℝ≥0∞) (u - a) =
      (ofMonotoneSubgroups N V hV).eFunctional ((2 ^ j : ℕ) : ℝ≥0∞) u := by
  rw [eFunctional_ofMonotoneSubgroups_two_pow, eFunctional_ofMonotoneSubgroups_two_pow]
  refine le_antisymm (le_iInf₂ fun b hb => ?_) (le_iInf₂ fun b hb => ?_)
  · exact iInf₂_le_of_le (b - a) (sub_mem hb ha) (by rw [sub_sub, add_sub_cancel])
  · exact iInf₂_le_of_le (a + b) (add_mem ha hb) (by rw [sub_sub])

end InterpCouple

/-! ### The complexity couple of an approximation scheme -/

namespace ApproximationScheme

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (A : ApproximationScheme X)

/-- The **complexity couple** of an approximation scheme: the norm of `X` and the complexity
`min {n : b ∈ A n}`. -/
noncomputable def complexityCouple : InterpCouple X :=
  InterpCouple.complexity (fun f => ‖f‖ₑ) A.sets

variable {A} {s : ℝ} {q : ℝ≥0∞}

/-- **The E-functional of the complexity couple is the error of best approximation**:
`E(n, f) = E_n(f)` for every `n ∈ ℕ`. -/
theorem eFunctional_complexityCouple (n : ℕ) (f : X) :
    A.complexityCouple.eFunctional n f = A.approxError f n := by
  rw [complexityCouple, InterpCouple.eFunctional_complexity_natCast A.mono, approxError,
    Metric.infEDist]
  simp only [eDist_eq_eNorm_sub]

/-- The dyadic norm of the complexity couple is the dyadic quasi-norm
`‖f‖ + ‖(2^(ks) E_{2^k}(f))_k‖_{ℓ_q}` of `A^s_q`. -/
theorem eNormDyadic_complexityCouple (f : X) :
    A.complexityCouple.eNormDyadic s q f = A.approxNormDyadic s q f := by
  simp only [InterpCouple.eNormDyadic, eFunctional_complexityCouple, approxNormDyadic]
  rfl

/-- **`E_{s,q}` of the complexity couple is the approximation space** (the E-method for
approximation schemes): for `s ≥ 0` and `q ≠ 0` with `s > 0` or `q = ∞`, `f ∈ E_{s,q}` iff
`f ∈ A^s_q`. -/
theorem memEMethod_complexityCouple_iff (hs : 0 ≤ s) (hsq : 0 < s ∨ q = ∞) (hq0 : q ≠ 0)
    {f : X} : A.complexityCouple.MemEMethod s q f ↔ A.MemApprox s q f := by
  have h1 : A.complexityCouple.norm1 0 = 0 := InterpCouple.complexity_norm1_zero (A.zero_mem 0)
  have hdisc : ∀ b, A.complexityCouple.norm1 b < 1 → b = 0 := fun _ hb =>
    InterpCouple.eq_zero_of_complexity_norm1_lt_one A.sets_zero hb
  rw [InterpCouple.memEMethod_iff_eNormDyadic_lt_top h1 hdisc hs hsq hq0,
    eNormDyadic_complexityCouple, memApprox_iff_approxNormDyadic_lt_top' hq0 hs]

end ApproximationScheme
