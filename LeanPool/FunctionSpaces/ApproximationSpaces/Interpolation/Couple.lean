/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Interpolation.KMethod

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Couples of extended quasi-norms and their K-method

A **couple** on an additive commutative group `U` consists of two extended-valued functions
`N₀, N₁ : U → [0, ∞]` (`InterpCouple`). The laws in `InterpCouple.IsQuasiNormed` make the
finite loci `X_i = {N_i < ∞}` additive subgroups. With definite restrictions of the two
functions to these subgroups, they have the component quasi-norms of Bergh–Löfström,
Section 3.10, using a quasi-triangle constant at least one. Classical compatibility also
uses continuous embeddings into a common Hausdorff topological group, as in Sections
2.3 and 3.10. The Lean results state the quasi-norm laws and any homogeneity
(`InterpCouple.IsHomogeneous`) where they are needed.

The **K-functional** is `K(t, u) = inf_b (N₀(u - b) + t N₁(b))` (`InterpCouple.kFunctional`), the
**continuous K-method** is `‖u‖_{K,θ,q} = Φ_{θ,q}(K(·, u))` with the functional
`ApproximationScheme.phiFunctional` (`InterpCouple.kMethodNorm`, `InterpCouple.MemKMethod`), and
the **discrete K-method** on the grid `t = 2^(nρ)`, `n ∈ ℤ`, is
`‖(2^(-nρθ) K(2^(nρ), u))_n‖_{ℓ_q}` (`InterpCouple.discreteKMethodNorm`).  For `θ ≥ 0` and
`ρ > 0` both give the same space (`InterpCouple.memKMethod_iff_discreteKMethodNorm_lt_top`,
an extension of Bergh–Löfström, Lemma 3.1.3). Swapping the couple replaces `θ` by `1 - θ`
(`InterpCouple.discreteKMethodNorm_swap`); for a quasi-normed couple both K-norms satisfy a
quasi-triangle inequality (`InterpCouple.kMethodNorm_add_le`,
`InterpCouple.discreteKMethodNorm_add_le`), and for a quasi-normed homogeneous couple the space is
a real subspace (`InterpCouple.kMethodSpace`).  For an ordered quasi-normed couple
(`N₀ ≤ c N₁`, `InterpCouple.norm0_le_mul_kFunctional_one`), the norm
`N₀(u) + ‖(2^(kρθ) K(2^(-kρ), u))_{k ∈ ℕ}‖_{ℓ_q}` on the grid `t = 2^(-kρ)`
(`InterpCouple.interpNorm`) gives the same space for `θ > 0`, `ρ > 0` and `q ≠ 0`
(`InterpCouple.memKMethod_iff_interpNorm_lt_top`), with explicit constants in both directions
(`InterpCouple.kMethodNorm_le_interpNorm`, `InterpCouple.interpNorm_le_kMethodNorm`).

A bounded linear map `ι : Y → X` gives the couple `(X, ι(Y))` (`InterpCouple.ofMap`), whose
K-functional is `ApproximationScheme.kFunctional ι` for `0 < t < ∞`.  Hence its continuous
K-method and its norm on the grid `t = 2^(-kρ)` are `ApproximationScheme.kMethodNorm` and
`ApproximationScheme.interpNorm` (`InterpCouple.kMethodNorm_ofMap`,
`InterpCouple.interpNorm_ofMap`).

The encoding is that of `EQuasinorm.Couple` in the project *MultilinearInterpolation* (Bonn;
van Doorn, Portegies, Rothgang, Viana Reis; Apache 2.0) on a group instead of a monoid; its
`kNorm`, `kMethod` and `discreteKMethod` are `kFunctional`, `kMethodNorm` and
`discreteKMethodNorm` here (the last one with `ρ = 1`).
-/

@[expose] public section

open MeasureTheory Set Function
open scoped ENNReal
open ENNReal (lqNorm dyadicWeight LpAddConst dyadicGeomConst)

/-- An extended-valued encoding of a **couple** on an additive commutative group `U`.
Its two functions `N₀, N₁ : U → [0, ∞]` are arbitrary. Under `InterpCouple.IsQuasiNormed` the
finite loci are subgroups. With definite restrictions and a quasi-triangle constant at least
one they are quasi-normed abelian groups as in Bergh–Löfström, Section 3.10. The common
topological space for classical compatibility is described in Section 2.3.
`EQuasinorm.Couple` of *MultilinearInterpolation* (Bonn, Apache 2.0) carries its quasi-norm
axioms in the data. -/
structure InterpCouple (U : Type*) [AddCommGroup U] where
  /-- The first extended-valued function `N₀`. -/
  norm0 : U → ℝ≥0∞
  /-- The second extended-valued function `N₁`. -/
  norm1 : U → ℝ≥0∞

namespace InterpCouple

variable {U : Type*} [AddCommGroup U]

/-! ### Swapping, quasi-norms and homogeneity -/

/-- The **swapped couple** `(N₁, N₀)`. -/
def swap (A : InterpCouple U) : InterpCouple U := ⟨A.norm1, A.norm0⟩

/-- The first norm of the swapped couple is `N₁`. -/
@[simp]
theorem swap_norm0 (A : InterpCouple U) : A.swap.norm0 = A.norm1 := rfl

/-- The second norm of the swapped couple is `N₀`. -/
@[simp]
theorem swap_norm1 (A : InterpCouple U) : A.swap.norm1 = A.norm0 := rfl

/-- Swapping twice gives the couple back. -/
@[simp]
theorem swap_swap (A : InterpCouple U) : A.swap.swap = A := rfl

/-- The couple is **quasi-normed with constant `C`**: `C < ∞`, and both `N_i` vanish at `0`,
are even and satisfy the quasi-triangle inequality `N_i(a + b) ≤ C (N_i(a) + N_i(b))`.
On the finite loci, adding definiteness and replacing `C` by `max 1 C` gives the axioms in
Bergh–Löfström, Section 3.10. The zero and quasi-triangle axioms also appear in
`EQuasinorm` in *MultilinearInterpolation*, which uses a monoid and assumes `C ≥ 1`. -/
structure IsQuasiNormed (A : InterpCouple U) (C : ℝ≥0∞) : Prop where
  /-- The quasi-triangle constant is finite. -/
  ne_top : C ≠ ∞
  /-- `N₀(0) = 0`. -/
  norm0_zero : A.norm0 0 = 0
  /-- `N₁(0) = 0`. -/
  norm1_zero : A.norm1 0 = 0
  /-- `N₀(-a) = N₀(a)`. -/
  norm0_neg (a : U) : A.norm0 (-a) = A.norm0 a
  /-- `N₁(-a) = N₁(a)`. -/
  norm1_neg (a : U) : A.norm1 (-a) = A.norm1 a
  /-- The quasi-triangle inequality for `N₀`. -/
  norm0_add_le (a b : U) : A.norm0 (a + b) ≤ C * (A.norm0 a + A.norm0 b)
  /-- The quasi-triangle inequality for `N₁`. -/
  norm1_add_le (a b : U) : A.norm1 (a + b) ≤ C * (A.norm1 a + A.norm1 b)

/-- The swapped couple of a quasi-normed couple is quasi-normed with the same constant. -/
theorem IsQuasiNormed.swap {A : InterpCouple U} {C : ℝ≥0∞} (hA : A.IsQuasiNormed C) :
    A.swap.IsQuasiNormed C :=
  ⟨hA.ne_top, hA.norm1_zero, hA.norm0_zero, hA.norm1_neg, hA.norm0_neg, hA.norm1_add_le,
    hA.norm0_add_le⟩

/-- The couple is **homogeneous** on a real vector space: `N_i(c a) ≤ |c| N_i(a)` for every real
`c` (hence equality for `c ≠ 0`). -/
structure IsHomogeneous [Module ℝ U] (A : InterpCouple U) : Prop where
  /-- Homogeneity of `N₀`. -/
  norm0_smul_le (c : ℝ) (a : U) : A.norm0 (c • a) ≤ ‖c‖ₑ * A.norm0 a
  /-- Homogeneity of `N₁`. -/
  norm1_smul_le (c : ℝ) (a : U) : A.norm1 (c • a) ≤ ‖c‖ₑ * A.norm1 a

/-- A homogeneous couple has `N₀(0) = 0`, from `c = 0`. -/
theorem IsHomogeneous.norm0_zero [Module ℝ U] {A : InterpCouple U} (hH : A.IsHomogeneous) :
    A.norm0 0 = 0 := by
  simpa using hH.norm0_smul_le 0 0

/-- A homogeneous couple has `N₁(0) = 0`, from `c = 0`. -/
theorem IsHomogeneous.norm1_zero [Module ℝ U] {A : InterpCouple U} (hH : A.IsHomogeneous) :
    A.norm1 0 = 0 := by
  simpa using hH.norm1_smul_le 0 0

/-! ### The K-functional -/

/-- The **K-functional** of the couple, `K(t, u) = inf_b (N₀(u - b) + t N₁(b))`.
For a classical compatible couple and `0 < t < ∞`, the finite contributions are exactly
the decompositions used in Bergh–Löfström, Section 3.1. The Lean definition also allows
`t = 0` and `t = ∞`. At `t = 0`, `0 * ∞ = 0` allows a candidate with `N₁(b) = ∞` to
contribute. At `t = ∞`, the penalty vanishes exactly when `N₁(b) = 0`.
This formula is `kNorm` in *MultilinearInterpolation*, expressed there using `u = a + b`. -/
noncomputable def kFunctional (A : InterpCouple U) (t : ℝ≥0∞) (u : U) : ℝ≥0∞ :=
  ⨅ b : U, A.norm0 (u - b) + t * A.norm1 b

variable {A : InterpCouple U} {t s c C : ℝ≥0∞}

/-- Every decomposition bounds the K-functional: `K(t, u) ≤ N₀(u - b) + t N₁(b)` (Bonn's
`kNorm_le_of_decomp`). -/
theorem kFunctional_le (b u : U) : A.kFunctional t u ≤ A.norm0 (u - b) + t * A.norm1 b :=
  iInf_le (fun b => A.norm0 (u - b) + t * A.norm1 b) b

/-- **An upper bound by decompositions passes to the K-functional**: if
`F ≤ X + c (N₀(u - b) + t N₁(b))` for every `b` and `c < ∞`, then `F ≤ X + c K(t, u)`, since
`b ↦ X + c (N₀(u - b) + t N₁(b))` has the infimum `X + c K(t, u)`. -/
theorem le_add_mul_kFunctional {F X : ℝ≥0∞} (hc : c ≠ ∞) {u : U}
    (h : ∀ b, F ≤ X + c * (A.norm0 (u - b) + t * A.norm1 b)) : F ≤ X + c * A.kFunctional t u := by
  rw [kFunctional, ENNReal.mul_iInf fun h' => absurd h' hc, ENNReal.add_iInf]
  exact le_iInf h

/-- `K(t, u) ≤ N₀(u)` if `N₁(0) = 0`, from `b = 0`. -/
theorem kFunctional_le_norm0 (h : A.norm1 0 = 0) (u : U) : A.kFunctional t u ≤ A.norm0 u :=
  (kFunctional_le 0 u).trans_eq (by rw [sub_zero, h, mul_zero, add_zero])

/-- `K(t, u) ≤ t N₁(u)` if `N₀(0) = 0`, from `b = u`. -/
theorem kFunctional_le_mul_norm1 (h : A.norm0 0 = 0) (u : U) :
    A.kFunctional t u ≤ t * A.norm1 u :=
  (kFunctional_le u u).trans_eq (by rw [sub_self, h, zero_add])

/-- `K(t, 0) = 0` if both norms vanish at `0`. -/
theorem kFunctional_zero_right (h0 : A.norm0 0 = 0) (h1 : A.norm1 0 = 0) :
    A.kFunctional t 0 = 0 :=
  le_antisymm ((kFunctional_le_norm0 h1 0).trans_eq h0) bot_le

/-- The K-functional increases with `t`. -/
theorem kFunctional_mono (h : t ≤ s) (u : U) : A.kFunctional t u ≤ A.kFunctional s u :=
  iInf_mono fun _ => by gcongr

/-- The K-functional `t ↦ K(t, u)` is monotone (Bonn's `monotone_kNorm`). -/
theorem monotone_kFunctional (u : U) : Monotone fun t => A.kFunctional t u :=
  fun _ _ h => kFunctional_mono h u

/-- **The K-functional under a finite change of scale**. The bound
`K(c t, u) ≤ max(1, c) K(t, u)` extends Bergh–Löfström, Lemma 3.1.1, to `c = 0` and to
the endpoint scales `t = 0, ∞` of the extended-valued definition. See also Bonn's
`kNorm_le_mul`. -/
theorem kFunctional_mul_le_of_ne_top (hc : c ≠ ∞) (t : ℝ≥0∞) (u : U) :
    A.kFunctional (c * t) u ≤ max 1 c * A.kFunctional t u := by
  have hM0 : max 1 c ≠ 0 := (zero_lt_one.trans_le (le_max_left _ _)).ne'
  have hMt : max 1 c ≠ ∞ := max_ne_top ENNReal.one_ne_top hc
  have h : max 1 c * A.kFunctional t u = ⨅ b, max 1 c * (A.norm0 (u - b) + t * A.norm1 b) :=
    ENNReal.mul_iInf_of_ne hM0 hMt
  rw [h]
  refine iInf_mono fun b => ?_
  rw [mul_add, mul_assoc c]
  gcongr
  · exact le_mul_of_one_le_left' (le_max_left _ _)
  · exact le_max_right _ _

/-- The pointwise bound behind the quasi-triangle inequality of the K-functional: for all
`b, b'`, `K(t, u + v) ≤ C ((N₀(u - b) + t N₁(b)) + (N₀(v - b') + t N₁(b')))`. -/
theorem kFunctional_add_le_of_decomp (hA : A.IsQuasiNormed C) (u v b b' : U) :
    A.kFunctional t (u + v) ≤
      C * ((A.norm0 (u - b) + t * A.norm1 b) + (A.norm0 (v - b') + t * A.norm1 b')) :=
  calc A.kFunctional t (u + v) ≤ A.norm0 ((u - b) + (v - b')) + t * A.norm1 (b + b') := by
        rw [← add_sub_add_comm]
        exact kFunctional_le _ _
    _ ≤ C * (A.norm0 (u - b) + A.norm0 (v - b')) + t * (C * (A.norm1 b + A.norm1 b')) := by
        gcongr
        · exact hA.norm0_add_le _ _
        · exact hA.norm1_add_le _ _
    _ = _ := by ring

/-- **The quasi-triangle inequality of the K-functional**. For a couple quasi-normed with
constant `C`, the bound `K(t, u + v) ≤ C (K(t, u) + K(t, v))` includes the extended-valued
endpoints. The common-constant case at positive finite scales is in Bergh–Löfström,
Lemma 3.11.1. See also Bonn's `kNorm_add_le_mul`. -/
theorem kFunctional_add_le (hA : A.IsQuasiNormed C) (u v : U) :
    A.kFunctional t (u + v) ≤ C * (A.kFunctional t u + A.kFunctional t v) := by
  rcases eq_or_ne C 0 with rfl | hC0
  · simpa using kFunctional_add_le_of_decomp hA u v 0 0
  have hu : C * A.kFunctional t u = ⨅ b, C * (A.norm0 (u - b) + t * A.norm1 b) :=
    ENNReal.mul_iInf_of_ne hC0 hA.ne_top
  have hv : C * A.kFunctional t v = ⨅ b, C * (A.norm0 (v - b) + t * A.norm1 b) :=
    ENNReal.mul_iInf_of_ne hC0 hA.ne_top
  rw [mul_add, hu, hv]
  exact ENNReal.le_iInf_add_iInf fun b b' =>
    (kFunctional_add_le_of_decomp hA u v b b').trans_eq (mul_add _ _ _)

/-- The K-functional of a couple of even functions is even: `K(t, -u) = K(t, u)` if
`N₀(-a) = N₀(a)` and `N₁(-a) = N₁(a)` for every `a`, by the substitution `b ↦ -b`.  For a
quasi-normed couple `hA` the hypotheses are `hA.norm0_neg` and `hA.norm1_neg`. -/
theorem kFunctional_neg (h0 : ∀ a, A.norm0 (-a) = A.norm0 a) (h1 : ∀ a, A.norm1 (-a) = A.norm1 a)
    (u : U) : A.kFunctional t (-u) = A.kFunctional t u := by
  refine Equiv.iInf_congr (Equiv.neg U) fun b => ?_
  rw [Equiv.neg_apply, h1, ← h0 (-u - b), show -(-u - b) = u - -b by abel]

/-- **Homogeneity of the K-functional**: `K(t, c u) ≤ |c| K(t, u)` for a homogeneous couple. -/
theorem kFunctional_smul_le [Module ℝ U] (hH : A.IsHomogeneous) (c : ℝ) (u : U) :
    A.kFunctional t (c • u) ≤ ‖c‖ₑ * A.kFunctional t u := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul, kFunctional_zero_right hH.norm0_zero hH.norm1_zero]
    exact zero_le
  have h : ‖c‖ₑ * A.kFunctional t u = ⨅ b, ‖c‖ₑ * (A.norm0 (u - b) + t * A.norm1 b) :=
    ENNReal.mul_iInf_of_ne (eNorm_ne_zero.2 hc) eNorm_ne_top
  rw [h]
  refine le_iInf fun b => ?_
  calc A.kFunctional t (c • u) ≤ A.norm0 (c • u - c • b) + t * A.norm1 (c • b) :=
        kFunctional_le _ _
    _ ≤ ‖c‖ₑ * A.norm0 (u - b) + t * (‖c‖ₑ * A.norm1 b) := by
        rw [← smul_sub]
        gcongr
        · exact hH.norm0_smul_le c _
        · exact hH.norm1_smul_le c _
    _ = ‖c‖ₑ * (A.norm0 (u - b) + t * A.norm1 b) := by ring

/-- **The K-functional of the swapped couple** (Bonn's `kNorm_swap`): for `0 < t < ∞`,
`K(t, u; N₁, N₀) = t K(t⁻¹, u; N₀, N₁)`, by the substitution `b ↦ u - b`. -/
theorem kFunctional_swap (ht0 : t ≠ 0) (ht : t ≠ ∞) (u : U) :
    A.swap.kFunctional t u = t * A.kFunctional t⁻¹ u := by
  have h : t * A.kFunctional t⁻¹ u = ⨅ b, t * (A.norm0 (u - b) + t⁻¹ * A.norm1 b) :=
    ENNReal.mul_iInf_of_ne ht0 ht
  rw [h]
  refine Equiv.iInf_congr (Equiv.subLeft u) fun b => ?_
  rw [Equiv.subLeft_apply, sub_sub_cancel, mul_add, ← mul_assoc, ENNReal.mul_inv_cancel ht0 ht,
    one_mul, add_comm]
  rfl

/-- **The first norm of an ordered couple by the K-functional at `t = 1`**: if the couple is
quasi-normed with constant `C` and `N₀ ≤ c N₁` with `c < ∞`, then
`N₀(u) ≤ C max(1, c) K(1, u)`, since `N₀(u) ≤ C (N₀(u - b) + c N₁(b))` for every `b`. -/
theorem norm0_le_mul_kFunctional_one (hA : A.IsQuasiNormed C) (hc : c ≠ ∞)
    (hord : ∀ a, A.norm0 a ≤ c * A.norm1 a) (u : U) :
    A.norm0 u ≤ C * max 1 c * A.kFunctional 1 u := by
  have hM : C * max 1 c ≠ ∞ := ENNReal.mul_ne_top hA.ne_top (max_ne_top ENNReal.one_ne_top hc)
  rw [kFunctional, ENNReal.mul_iInf fun h => absurd h hM]
  refine le_iInf fun b => ?_
  calc A.norm0 u = A.norm0 ((u - b) + b) := by rw [sub_add_cancel]
    _ ≤ C * (A.norm0 (u - b) + A.norm0 b) := hA.norm0_add_le _ _
    _ ≤ C * (max 1 c * A.norm0 (u - b) + max 1 c * (1 * A.norm1 b)) := by
        gcongr
        · exact le_mul_of_one_le_left' (le_max_left _ _)
        · rw [one_mul]
          exact (hord b).trans (by gcongr; exact le_max_right _ _)
    _ = C * max 1 c * (A.norm0 (u - b) + 1 * A.norm1 b) := by ring

/-! ### The continuous and the discrete K-method -/

variable {θ ρ : ℝ} {q : ℝ≥0∞}

/-- The norm of the **continuous K-method** of the couple, `‖u‖_{K,θ,q} = Φ_{θ,q}(K(·, u))`,
that is `(∫_0^∞ (t^(-θ) K(t, u))^q dt/t)^(1/q)` for `0 < q < ∞`, the essential supremum of
`t^(-θ) K(t, u)` for `q = ∞`, and `0` for `q = 0` by the `eLpNorm` convention.
Bergh–Löfström, Sections 3.1 and 3.11, describe the classical norm and quasi-norm ranges.
The definition here takes arbitrary real `θ` and uses the functional of Bonn's `kMethod`. -/
noncomputable def kMethodNorm (A : InterpCouple U) (θ : ℝ) (q : ℝ≥0∞) (u : U) : ℝ≥0∞ :=
  ApproximationScheme.phiFunctional θ q fun t => A.kFunctional t u

/-- `u` belongs to the **real interpolation space** `(X₀, X₁)_{θ,q}` of the couple:
`‖u‖_{K,θ,q} < ∞`. -/
def MemKMethod (A : InterpCouple U) (θ : ℝ) (q : ℝ≥0∞) (u : U) : Prop :=
  A.kMethodNorm θ q u < ∞

/-- The sequence `(2^(-nρθ) K(2^(nρ), u))_{n ∈ ℤ}` of the discrete K-method on the grid
`t = 2^(nρ)`. -/
noncomputable def discreteKSeq (A : InterpCouple U) (θ ρ : ℝ) (u : U) (n : ℤ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ (-((n : ℝ) * ρ * θ)) * A.kFunctional ((2 : ℝ≥0∞) ^ ((n : ℝ) * ρ)) u

/-- The norm of the **discrete K-method** on the grid `t = 2^(nρ)`, `n ∈ ℤ`:
`‖(2^(-nρθ) K(2^(nρ), u))_{n ∈ ℤ}‖_{ℓ_q}`.  For `ρ = 1` it is the norm of Bonn's
`discreteKMethod`. -/
noncomputable def discreteKMethodNorm (A : InterpCouple U) (θ ρ : ℝ) (q : ℝ≥0∞) (u : U) :
    ℝ≥0∞ :=
  lqNorm q (A.discreteKSeq θ ρ u)

/-- The discrete K-norm is the `ℓ_q` norm of `ApproximationScheme.discretePhiSeq θ ρ` for
`φ = K(·, u)`. -/
theorem discreteKMethodNorm_eq (u : U) : A.discreteKMethodNorm θ ρ q u =
    lqNorm q (ApproximationScheme.discretePhiSeq θ ρ fun t => A.kFunctional t u) := rfl

/-- The term with `n = 0` is `K(1, u)`. -/
theorem discreteKSeq_zero (u : U) : A.discreteKSeq θ ρ u 0 = A.kFunctional 1 u :=
  ApproximationScheme.discretePhiSeq_zero fun t => A.kFunctional t u

/-- The term `n` of the discrete K-method on the grid `t = 2^n`:
`2^(-nθ) K(2^n, u)`. -/
theorem discreteKSeq_one (u : U) (n : ℤ) :
    A.discreteKSeq θ 1 u n = 2 ^ (-((n : ℝ) * θ)) * A.kFunctional (2 ^ (n : ℝ)) u := by
  simp only [discreteKSeq, mul_one]

/-- **The continuous K-norm by the discrete one**: for `θ ≥ 0` and `ρ > 0`,
`‖u‖_{K,θ,q} ≤ (ρ log 2)^(1/q) 2^(ρθ) ‖(2^(-nρθ) K(2^(nρ), u))_{n ∈ ℤ}‖_{ℓ_q}`. -/
theorem kMethodNorm_le_discreteKMethodNorm (hθ : 0 ≤ θ) (hρ : 0 < ρ) (u : U) :
    A.kMethodNorm θ q u ≤ ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal) *
      (2 ^ (ρ * θ) * A.discreteKMethodNorm θ ρ q u) := by
  rw [discreteKMethodNorm_eq]
  exact ApproximationScheme.phiFunctional_le_lqNorm_discretePhiSeq
    (monotone_kFunctional (A := A) u) hθ hρ

/-- **The discrete K-norm by the continuous one**: for `θ ≥ 0` and `ρ > 0`,
`(ρ log 2)^(1/q) 2^(-ρθ) ‖(2^(-nρθ) K(2^(nρ), u))_{n ∈ ℤ}‖_{ℓ_q} ≤ ‖u‖_{K,θ,q}`. -/
theorem discreteKMethodNorm_le_kMethodNorm (hθ : 0 ≤ θ) (hρ : 0 < ρ) (u : U) :
    ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal) *
      (2 ^ (-(ρ * θ)) * A.discreteKMethodNorm θ ρ q u) ≤ A.kMethodNorm θ q u := by
  rw [discreteKMethodNorm_eq]
  exact ApproximationScheme.lqNorm_discretePhiSeq_le_phiFunctional
    (monotone_kFunctional (A := A) u) hθ hρ

/-- **The discrete K-norm by the continuous one, solved for the discrete norm**: for `θ ≥ 0` and
`ρ > 0`, `‖(2^(-nρθ) K(2^(nρ), u))_{n ∈ ℤ}‖_{ℓ_q} ≤ ((ρ log 2)^(1/q) 2^(-ρθ))⁻¹ ‖u‖_{K,θ,q}`
(`discreteKMethodNorm_le_kMethodNorm`). -/
theorem discreteKMethodNorm_le_inv_mul_kMethodNorm (hθ : 0 ≤ θ) (hρ : 0 < ρ) (u : U) :
    A.discreteKMethodNorm θ ρ q u ≤
      (ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal) * 2 ^ (-(ρ * θ)))⁻¹ *
        A.kMethodNorm θ q u := by
  rw [discreteKMethodNorm_eq]
  exact ApproximationScheme.lqNorm_discretePhiSeq_le_inv_mul_phiFunctional
    (monotone_kFunctional (A := A) u) hθ hρ

/-- The continuous K-norm by the discrete K-norm on the grid `t = 2^n`: for `θ ≥ 0`,
`‖u‖_{K,θ,q} ≤ (log 2)^(1/q) 2^θ ‖u‖_{θ,1,q}` (`kMethodNorm_le_discreteKMethodNorm` with
`ρ = 1`). -/
theorem kMethodNorm_le_mul_discreteKMethodNorm (hθ : 0 ≤ θ) (u : U) :
    A.kMethodNorm θ q u ≤
      ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal) * 2 ^ θ * A.discreteKMethodNorm θ 1 q u := by
  have h := kMethodNorm_le_discreteKMethodNorm (A := A) (q := q) hθ one_pos u
  simpa only [one_mul, mul_assoc] using h

/-- The discrete K-norm on the grid `t = 2^n` by the continuous K-norm: for `θ ≥ 0`,
`‖u‖_{θ,1,q} ≤ ((log 2)^(1/q) 2^(-θ))⁻¹ ‖u‖_{K,θ,q}` (`discreteKMethodNorm_le_inv_mul_kMethodNorm`
with `ρ = 1`). -/
theorem discreteKMethodNorm_le_mul_kMethodNorm (hθ : 0 ≤ θ) (u : U) :
    A.discreteKMethodNorm θ 1 q u ≤
      (ENNReal.ofReal (Real.log 2) ^ (1 / q.toReal) * 2 ^ (-θ))⁻¹ * A.kMethodNorm θ q u := by
  simpa only [one_mul] using discreteKMethodNorm_le_inv_mul_kMethodNorm (A := A) (q := q) hθ
    one_pos u

/-- **The discrete and the continuous K-method agree**. Bergh–Löfström, Lemma 3.1.3,
uses the two-sided grid `2^n` in the classical interpolation range. This version allows
`θ ≥ 0`, any two-sided grid `2^(nρ)` with `ρ > 0`, and every `q`, including the zero-exponent
convention. Then `‖u‖_{K,θ,q} < ∞` iff `‖(2^(-nρθ) K(2^(nρ), u))_{n ∈ ℤ}‖_{ℓ_q} < ∞`.
See also Bonn's `discreteKMethod_equiv_kmethod`. -/
theorem memKMethod_iff_discreteKMethodNorm_lt_top (hθ : 0 ≤ θ) (hρ : 0 < ρ) {u : U} :
    A.MemKMethod θ q u ↔ A.discreteKMethodNorm θ ρ q u < ∞ := by
  have hc0 := ApproximationScheme.ofReal_mul_log_two_rpow_ne_zero hρ q
  have hct : ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have h2 : (2 : ℝ≥0∞) ^ (-(ρ * θ)) ≠ 0 := (ENNReal.rpow_pos two_pos ENNReal.ofNat_ne_top).ne'
  exact ⟨fun h => ENNReal.lt_top_of_mul_ne_top_right (ENNReal.lt_top_of_mul_ne_top_right
      ((discreteKMethodNorm_le_kMethodNorm hθ hρ u).trans_lt h).ne hc0).ne h2,
    fun h => (kMethodNorm_le_discreteKMethodNorm hθ hρ u).trans_lt (ENNReal.mul_lt_top hct.lt_top
      (ENNReal.mul_lt_top (ENNReal.two_rpow_ne_top _).lt_top h))⟩

/-- **The discrete K-method of the swapped couple**, termwise: the term `n` for `(N₁, N₀)` and
`θ` is the term `-n` for `(N₀, N₁)` and `1 - θ`, by `kFunctional_swap`. -/
theorem discreteKSeq_swap (u : U) (n : ℤ) :
    A.swap.discreteKSeq θ ρ u n = A.discreteKSeq (1 - θ) ρ u (-n) := by
  have h0 : (2 : ℝ≥0∞) ^ ((n : ℝ) * ρ) ≠ 0 := (ENNReal.rpow_pos two_pos ENNReal.ofNat_ne_top).ne'
  have ht : (2 : ℝ≥0∞) ^ ((n : ℝ) * ρ) ≠ ∞ := ENNReal.two_rpow_ne_top _
  have e1 : -((n : ℝ) * ρ * θ) + (n : ℝ) * ρ = -(((-n : ℤ) : ℝ) * ρ * (1 - θ)) := by
    push_cast
    ring
  have e2 : -((n : ℝ) * ρ) = ((-n : ℤ) : ℝ) * ρ := by
    push_cast
    ring
  rw [discreteKSeq, discreteKSeq, kFunctional_swap h0 ht, ← ENNReal.rpow_neg, ← mul_assoc,
    ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top, e1, e2]

/-- **Swapping the couple replaces `θ` by `1 - θ`** (Bonn's `enorm_discreteKMethod_swap`):
the discrete K-norm of `(N₁, N₀)` with `θ` is that of `(N₀, N₁)` with `1 - θ`, on every grid
`t = 2^(nρ)`. -/
theorem discreteKMethodNorm_swap (u : U) :
    A.swap.discreteKMethodNorm θ ρ q u = A.discreteKMethodNorm (1 - θ) ρ q u := by
  have h : A.swap.discreteKSeq θ ρ u = A.discreteKSeq (1 - θ) ρ u ∘ Equiv.neg ℤ :=
    funext fun n => discreteKSeq_swap u n
  rw [discreteKMethodNorm, discreteKMethodNorm, h, ENNReal.lqNorm_comp_equiv]

/-- **The K-functional by the discrete K-norm** (the class `C_K(θ)` of Bergh–Löfström,
Definition 3.5.1, in discrete form): for `q ≠ 0` and every `n ∈ ℤ`,
`K(2^(nρ), u) ≤ 2^(nρθ) ‖(2^(-mρθ) K(2^(mρ), u))_{m ∈ ℤ}‖_{ℓ_q}`. -/
theorem kFunctional_le_discreteKMethodNorm (hq : q ≠ 0) (n : ℤ) (u : U) :
    A.kFunctional ((2 : ℝ≥0∞) ^ ((n : ℝ) * ρ)) u ≤
      (2 : ℝ≥0∞) ^ ((n : ℝ) * ρ * θ) * A.discreteKMethodNorm θ ρ q u := by
  calc A.kFunctional ((2 : ℝ≥0∞) ^ ((n : ℝ) * ρ)) u
      = (2 : ℝ≥0∞) ^ ((n : ℝ) * ρ * θ) * A.discreteKSeq θ ρ u n := by
        rw [discreteKSeq, ← mul_assoc, ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top,
          add_neg_cancel, ENNReal.rpow_zero, one_mul]
    _ ≤ _ := by
        gcongr
        exact ENNReal.le_lqNorm hq _ n

/-- The class `C_K` on the grid `t = 2^n`: `K(2^n, u) ≤ 2^(nθ) ‖u‖_{θ,1,q}` for every `n ∈ ℤ`
and `q ≠ 0` (`kFunctional_le_discreteKMethodNorm` with `ρ = 1`). -/
theorem kFunctional_two_rpow_le_discreteKMethodNorm (hq : q ≠ 0) (n : ℤ) (u : U) :
    A.kFunctional (2 ^ (n : ℝ)) u ≤ 2 ^ ((n : ℝ) * θ) * A.discreteKMethodNorm θ 1 q u := by
  simpa only [mul_one] using kFunctional_le_discreteKMethodNorm (A := A) (ρ := 1) (θ := θ) hq n u

/-- The integrand of the continuous K-norm of `u` as a function of `t : ℝ`; it is measurable,
since `K(·, u)` is monotone. -/
theorem aestronglyMeasurable_phiIntegrand_kFunctional (u : U) :
    AEStronglyMeasurable (ApproximationScheme.phiIntegrand θ fun t => A.kFunctional t u)
      ApproximationScheme.kMethodMeasure :=
  (ApproximationScheme.measurable_phiIntegrand (monotone_kFunctional u)).aestronglyMeasurable

/-- **The quasi-triangle inequality of the continuous K-norm** extends the estimate from
Bergh–Löfström, Section 3.11, to arbitrary real `θ` and includes the case `q = 0`.
For a couple quasi-normed with constant `C`,
`‖u + v‖_{K,θ,q} ≤ C_q C (‖u‖_{K,θ,q} + ‖v‖_{K,θ,q})`, where `C_q` is Mathlib's constant
`LpAddConst q` (`1` for `q ≥ 1`). -/
theorem kMethodNorm_add_le (hA : A.IsQuasiNormed C) (u v : U) :
    A.kMethodNorm θ q (u + v) ≤ LpAddConst q * C * (A.kMethodNorm θ q u + A.kMethodNorm θ q v) := by
  rw [kMethodNorm, kMethodNorm, kMethodNorm, ApproximationScheme.phiFunctional_eq,
    ApproximationScheme.phiFunctional_eq, ApproximationScheme.phiFunctional_eq]
  calc eLpNorm (ApproximationScheme.phiIntegrand θ fun t => A.kFunctional t (u + v)) q
        ApproximationScheme.kMethodMeasure
      ≤ C * eLpNorm ((ApproximationScheme.phiIntegrand θ fun t => A.kFunctional t u) +
          ApproximationScheme.phiIntegrand θ fun t => A.kFunctional t v) q
          ApproximationScheme.kMethodMeasure := by
        refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' q
          (aestronglyMeasurable_phiIntegrand_kFunctional _) (Filter.Eventually.of_forall
            fun t => ?_)
        simp only [eNorm_eq_self, Pi.add_apply, ApproximationScheme.phiIntegrand]
        calc ENNReal.ofReal t ^ (-θ) * A.kFunctional (ENNReal.ofReal t) (u + v)
            ≤ ENNReal.ofReal t ^ (-θ) * (C * (A.kFunctional (ENNReal.ofReal t) u +
                A.kFunctional (ENNReal.ofReal t) v)) := by
              gcongr
              exact kFunctional_add_le hA u v
          _ = _ := by ring
    _ ≤ C * (LpAddConst q * (eLpNorm (ApproximationScheme.phiIntegrand θ fun t =>
            A.kFunctional t u) q ApproximationScheme.kMethodMeasure +
          eLpNorm (ApproximationScheme.phiIntegrand θ fun t => A.kFunctional t v) q
            ApproximationScheme.kMethodMeasure)) := by
        gcongr
        exact eLpNorm_add_le' q
    _ = _ := by ring

/-- **Homogeneity of the continuous K-norm**: `‖c u‖_{K,θ,q} ≤ |c| ‖u‖_{K,θ,q}` for a
homogeneous couple. -/
theorem kMethodNorm_smul_le [Module ℝ U] (hH : A.IsHomogeneous) (c : ℝ) (u : U) :
    A.kMethodNorm θ q (c • u) ≤ ‖c‖ₑ * A.kMethodNorm θ q u := by
  rw [kMethodNorm, kMethodNorm, ApproximationScheme.phiFunctional_eq,
    ApproximationScheme.phiFunctional_eq]
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' q
    (aestronglyMeasurable_phiIntegrand_kFunctional _) (Filter.Eventually.of_forall fun t => ?_)
  simp only [eNorm_eq_self, ApproximationScheme.phiIntegrand]
  calc ENNReal.ofReal t ^ (-θ) * A.kFunctional (ENNReal.ofReal t) (c • u)
      ≤ ENNReal.ofReal t ^ (-θ) * (‖c‖ₑ * A.kFunctional (ENNReal.ofReal t) u) := by
        gcongr
        exact kFunctional_smul_le hH c u
    _ = _ := by ring

/-- `‖0‖_{K,θ,q} = 0` if both norms vanish at `0`. -/
theorem kMethodNorm_zero (h0 : A.norm0 0 = 0) (h1 : A.norm1 0 = 0) :
    A.kMethodNorm θ q 0 = 0 := by
  simp [kMethodNorm, kFunctional_zero_right h0 h1, ApproximationScheme.phiFunctional]

/-- The discrete K-norm vanishes at `0` if both norms do. -/
theorem discreteKMethodNorm_zero (h0 : A.norm0 0 = 0) (h1 : A.norm1 0 = 0) :
    A.discreteKMethodNorm θ ρ q 0 = 0 := by
  have h : A.discreteKSeq θ ρ 0 = fun _ => 0 :=
    funext fun n => by rw [discreteKSeq, kFunctional_zero_right h0 h1, mul_zero]
  rw [discreteKMethodNorm, h, ENNReal.lqNorm_zero_right]

/-- The discrete K-norm of a couple of even functions is even. -/
theorem discreteKMethodNorm_neg (h0 : ∀ a, A.norm0 (-a) = A.norm0 a)
    (h1 : ∀ a, A.norm1 (-a) = A.norm1 a) (u : U) :
    A.discreteKMethodNorm θ ρ q (-u) = A.discreteKMethodNorm θ ρ q u := by
  have h : A.discreteKSeq θ ρ (-u) = A.discreteKSeq θ ρ u :=
    funext fun n => by rw [discreteKSeq, discreteKSeq, kFunctional_neg h0 h1]
  rw [discreteKMethodNorm, discreteKMethodNorm, h]

/-- **The quasi-triangle inequality of the discrete K-norm**: for a couple quasi-normed with
constant `C` and `1 ≤ q ≤ ∞`, `‖u + v‖_{θ,ρ,q} ≤ C (‖u‖_{θ,ρ,q} + ‖v‖_{θ,ρ,q})`, from the
quasi-triangle inequality of the K-functional and Minkowski's inequality. -/
theorem discreteKMethodNorm_add_le (hA : A.IsQuasiNormed C) (hq : 1 ≤ q) (u v : U) :
    A.discreteKMethodNorm θ ρ q (u + v) ≤
      C * (A.discreteKMethodNorm θ ρ q u + A.discreteKMethodNorm θ ρ q v) :=
  calc A.discreteKMethodNorm θ ρ q (u + v)
      ≤ lqNorm q (fun n => C * (A.discreteKSeq θ ρ u n + A.discreteKSeq θ ρ v n)) :=
        ENNReal.lqNorm_mono fun n => (mul_le_mul_right (kFunctional_add_le hA u v) _).trans_eq
          (by simp only [discreteKSeq]; ring)
    _ = C * lqNorm q (fun n => A.discreteKSeq θ ρ u n + A.discreteKSeq θ ρ v n) :=
        ENNReal.lqNorm_const_mul _ _
    _ ≤ _ := by
        gcongr
        exact ENNReal.lqNorm_add_le hq _ _

/-- The **real interpolation space** `(X₀, X₁)_{θ,q}` of a quasi-normed homogeneous couple, as a
real subspace of `U` (Bergh–Löfström, Sections 3.1 and 3.11). -/
def kMethodSpace [Module ℝ U] (hA : A.IsQuasiNormed C) (hH : A.IsHomogeneous) (θ : ℝ)
    (q : ℝ≥0∞) : Submodule ℝ U where
  carrier := {u | A.MemKMethod θ q u}
  zero_mem' := by
    change A.kMethodNorm θ q 0 < ∞
    rw [kMethodNorm_zero hA.norm0_zero hA.norm1_zero]
    exact ENNReal.zero_lt_top
  add_mem' hu hv := (kMethodNorm_add_le hA _ _).trans_lt (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.LpAddConst_lt_top q) hA.ne_top.lt_top)
    (ENNReal.add_lt_top.2 ⟨hu, hv⟩))
  smul_mem' c _ hu := (kMethodNorm_smul_le hH c _).trans_lt (ENNReal.mul_lt_top eNorm_lt_top hu)

/-- Membership in the real interpolation space as a submodule. -/
@[simp]
theorem mem_kMethodSpace [Module ℝ U] {hA : A.IsQuasiNormed C} {hH : A.IsHomogeneous} {u : U} :
    u ∈ kMethodSpace hA hH θ q ↔ A.MemKMethod θ q u := Iff.rfl

/-! ### The grid on `ℕ` with the term `N₀` -/

/-- The norm `N₀(u) + ‖(2^(kρθ) K(2^(-kρ), u))_{k ∈ ℕ}‖_{ℓ_q}` of the discrete K-method on the
grid `t = 2^(-kρ)`, `k ∈ ℕ`, as in `ApproximationScheme.interpNorm`. -/
noncomputable def interpNorm (A : InterpCouple U) (θ ρ : ℝ) (q : ℝ≥0∞) (u : U) : ℝ≥0∞ :=
  A.norm0 u + lqNorm q fun k : ℕ => dyadicWeight (ρ * θ) k * A.kFunctional (dyadicWeight (-ρ) k) u

/-- The norm on the grid `ℕ` vanishes at `0` if both norms do. -/
theorem interpNorm_zero (h0 : A.norm0 0 = 0) (h1 : A.norm1 0 = 0) : A.interpNorm θ ρ q 0 = 0 := by
  simp [interpNorm, h0, kFunctional_zero_right h0 h1, ENNReal.lqNorm_zero_right]

/-- **The discrete K-norm on `ℤ` by the norm on the grid `ℕ`**: if `N₁(0) = 0` and `ρθ ≥ 0`,
`‖(2^(-nρθ) K(2^(nρ), u))_{n ∈ ℤ}‖_{ℓ_q} ≤ C_q γ (N₀(u) + ‖(2^(kρθ) K(2^(-kρ), u))_k‖_{ℓ_q})`
with `γ = dyadicGeomConst (ρθ) q` and Mathlib's constant `C_q = LpAddConst q`. -/
theorem discreteKMethodNorm_le_interpNorm (h1 : A.norm1 0 = 0) (hρθ : 0 ≤ ρ * θ) (u : U) :
    A.discreteKMethodNorm θ ρ q u ≤
      LpAddConst q * dyadicGeomConst (ρ * θ) q * A.interpNorm θ ρ q u :=
  ApproximationScheme.lqNorm_discretePhiSeq_le (φ := fun t => A.kFunctional t u) hρθ
    fun _ => kFunctional_le_norm0 h1 u

/-- **The norm on the grid `ℕ` by the discrete K-norm on `ℤ`**, for an ordered couple: if the
couple is quasi-normed with constant `C`, `N₀ ≤ c N₁` with `c < ∞`, and `q ≠ 0`, then
`N₀(u) + ‖(2^(kρθ) K(2^(-kρ), u))_k‖_{ℓ_q} ≤ (1 + C max(1, c)) ‖(2^(-nρθ) K(2^(nρ), u))_n‖_{ℓ_q}`.
-/
theorem interpNorm_le_discreteKMethodNorm (hA : A.IsQuasiNormed C) (hc : c ≠ ∞)
    (hord : ∀ a, A.norm0 a ≤ c * A.norm1 a) (hq : q ≠ 0) (u : U) :
    A.interpNorm θ ρ q u ≤ (1 + C * max 1 c) * A.discreteKMethodNorm θ ρ q u := by
  have h1 : A.norm0 u ≤ C * max 1 c * A.discreteKMethodNorm θ ρ q u := by
    refine (norm0_le_mul_kFunctional_one hA hc hord u).trans ?_
    gcongr
    exact (discreteKSeq_zero u).symm.le.trans (ENNReal.le_lqNorm hq _ 0)
  have h2 : lqNorm q (fun k : ℕ => dyadicWeight (ρ * θ) k *
      A.kFunctional (dyadicWeight (-ρ) k) u) ≤ A.discreteKMethodNorm θ ρ q u :=
    ApproximationScheme.lqNorm_le_lqNorm_discretePhiSeq (φ := fun t => A.kFunctional t u)
  calc A.interpNorm θ ρ q u ≤ C * max 1 c * A.discreteKMethodNorm θ ρ q u +
        A.discreteKMethodNorm θ ρ q u := add_le_add h1 h2
    _ = (1 + C * max 1 c) * A.discreteKMethodNorm θ ρ q u := by ring

/-- **The continuous K-method and the grid on `ℕ`**, for an ordered couple: if the couple is
quasi-normed with constant `C` and `N₀ ≤ c N₁` with `c < ∞`, then for `θ > 0`, `ρ > 0` and
`q ≠ 0`, `‖u‖_{K,θ,q} < ∞` if and only if `N₀(u) + ‖(2^(kρθ) K(2^(-kρ), u))_k‖_{ℓ_q} < ∞`. -/
theorem memKMethod_iff_interpNorm_lt_top (hA : A.IsQuasiNormed C) (hc : c ≠ ∞)
    (hord : ∀ a, A.norm0 a ≤ c * A.norm1 a) (hθ : 0 < θ) (hρ : 0 < ρ) (hq : q ≠ 0) {u : U} :
    A.MemKMethod θ q u ↔ A.interpNorm θ ρ q u < ∞ := by
  rw [memKMethod_iff_discreteKMethodNorm_lt_top hθ.le hρ]
  have hM : 1 + C * max 1 c < ∞ := ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top,
    ENNReal.mul_lt_top hA.ne_top.lt_top (max_lt ENNReal.one_lt_top hc.lt_top)⟩
  have hL : LpAddConst q * dyadicGeomConst (ρ * θ) q < ∞ :=
    ENNReal.mul_lt_top (ENNReal.LpAddConst_lt_top q)
      (ENNReal.dyadicGeomConst_ne_top (mul_pos hρ hθ) q).lt_top
  exact ⟨fun h => (interpNorm_le_discreteKMethodNorm hA hc hord hq u).trans_lt
      (ENNReal.mul_lt_top hM h),
    fun h => (discreteKMethodNorm_le_interpNorm hA.norm1_zero (mul_pos hρ hθ).le u).trans_lt
      (ENNReal.mul_lt_top hL h)⟩

/-- **The continuous K-norm by the norm on the grid `ℕ`**: if `N₁(0) = 0`, `θ ≥ 0` and `ρ > 0`,
then `‖u‖_{K,θ,q} ≤ c (N₀(u) + ‖(2^(kρθ) K(2^(-kρ), u))_k‖_{ℓ_q})` with the constant
`c = ApproximationScheme.kMethodUpperConst θ ρ q` of the couples of bounded linear maps. -/
theorem kMethodNorm_le_interpNorm (h1 : A.norm1 0 = 0) (hθ : 0 ≤ θ) (hρ : 0 < ρ) (u : U) :
    A.kMethodNorm θ q u ≤ ApproximationScheme.kMethodUpperConst θ ρ q * A.interpNorm θ ρ q u :=
  calc A.kMethodNorm θ q u
      ≤ ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal) *
          (2 ^ (ρ * θ) * A.discreteKMethodNorm θ ρ q u) :=
        kMethodNorm_le_discreteKMethodNorm hθ hρ u
    _ ≤ ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal) * (2 ^ (ρ * θ) *
          (LpAddConst q * dyadicGeomConst (ρ * θ) q * A.interpNorm θ ρ q u)) := by
        gcongr
        exact discreteKMethodNorm_le_interpNorm h1 (mul_nonneg hρ.le hθ) u
    _ = ApproximationScheme.kMethodUpperConst θ ρ q * A.interpNorm θ ρ q u := by
        rw [ApproximationScheme.kMethodUpperConst]
        ring

/-- **The norm on the grid `ℕ` by the continuous K-norm**, for an ordered couple: if the couple
is quasi-normed with constant `C`, `N₀ ≤ c N₁` with `c < ∞`, `θ ≥ 0`, `ρ > 0` and `q ≠ 0`, then
`N₀(u) + ‖(2^(kρθ) K(2^(-kρ), u))_k‖_{ℓ_q} ≤ (1 + C max(1, c)) 2^(ρθ) (ρ log 2)^(-1/q)
‖u‖_{K,θ,q}`. -/
theorem interpNorm_le_kMethodNorm (hA : A.IsQuasiNormed C) (hc : c ≠ ∞)
    (hord : ∀ a, A.norm0 a ≤ c * A.norm1 a) (hθ : 0 ≤ θ) (hρ : 0 < ρ) (hq : q ≠ 0) (u : U) :
    A.interpNorm θ ρ q u ≤ (1 + C * max 1 c) *
      (2 ^ (ρ * θ) * (ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal))⁻¹) *
        A.kMethodNorm θ q u :=
  have hinv : (ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal) * 2 ^ (-(ρ * θ)))⁻¹ =
      2 ^ (ρ * θ) * (ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal))⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl (ApproximationScheme.ofReal_mul_log_two_rpow_ne_zero hρ q))
      (Or.inl (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)),
      ENNReal.rpow_neg, inv_inv, mul_comm]
  calc A.interpNorm θ ρ q u ≤ (1 + C * max 1 c) * A.discreteKMethodNorm θ ρ q u :=
        interpNorm_le_discreteKMethodNorm hA hc hord hq u
    _ ≤ (1 + C * max 1 c) * ((ENNReal.ofReal (ρ * Real.log 2) ^ (1 / q.toReal) *
          2 ^ (-(ρ * θ)))⁻¹ * A.kMethodNorm θ q u) := by
        gcongr
        exact discreteKMethodNorm_le_inv_mul_kMethodNorm hθ hρ u
    _ = _ := by rw [hinv]; ring

/-! ### The couple of a bounded linear map -/

section OfMap

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {ι : Y →L[ℝ] X}

/-- The **couple of a bounded linear map** `ι : Y → X`: `N₀(f) = ‖f‖` and
`N₁(f) = inf {‖y‖ : ι y = f}` (`∞` off the range of `ι`), so that the spaces are `X` and
`ι(Y)` with the quotient norm; `ι` need not be injective. -/
noncomputable def ofMap (ι : Y →L[ℝ] X) : InterpCouple X where
  norm0 f := ‖f‖ₑ
  norm1 f := ⨅ y : {y : Y // ι y = f}, ‖(y : Y)‖ₑ

/-- The first norm of `ofMap ι` is the norm of `X`. -/
theorem ofMap_norm0 (f : X) : (ofMap ι).norm0 f = ‖f‖ₑ := rfl

/-- The second norm of `ofMap ι` is the quotient norm `inf {‖y‖ : ι y = f}`. -/
theorem ofMap_norm1 (f : X) : (ofMap ι).norm1 f = ⨅ y : {y : Y // ι y = f}, ‖(y : Y)‖ₑ := rfl

/-- Every preimage bounds the quotient norm: `N₁(f) ≤ ‖y‖` if `ι y = f`. -/
theorem norm1_ofMap_le {y : Y} {f : X} (hy : ι y = f) : (ofMap ι).norm1 f ≤ ‖y‖ₑ :=
  iInf_le_of_le ⟨y, hy⟩ le_rfl

/-- The quotient norm of `-f` is at most that of `f`. -/
theorem norm1_ofMap_neg_le (f : X) : (ofMap ι).norm1 (-f) ≤ (ofMap ι).norm1 f :=
  le_iInf fun y => (norm1_ofMap_le (by rw [map_neg, y.2])).trans_eq (eNorm_neg _)

/-- The couple of a bounded linear map is quasi-normed with constant `1`. -/
theorem isQuasiNormed_ofMap : (ofMap ι).IsQuasiNormed 1 where
  ne_top := ENNReal.one_ne_top
  norm0_zero := eNorm_zero
  norm1_zero := nonpos_iff_eq_zero.1 ((norm1_ofMap_le (map_zero ι)).trans_eq eNorm_zero)
  norm0_neg := eNorm_neg
  norm1_neg f :=
    le_antisymm (norm1_ofMap_neg_le f) (by simpa using norm1_ofMap_neg_le (ι := ι) (-f))
  norm0_add_le f g := by
    rw [one_mul]
    exact eNorm_add_le f g
  norm1_add_le f g := by
    rw [one_mul]
    exact ENNReal.le_iInf_add_iInf fun y z =>
      (norm1_ofMap_le (by rw [map_add, y.2, z.2])).trans (eNorm_add_le _ _)

/-- The couple of a bounded linear map is homogeneous. -/
theorem isHomogeneous_ofMap : (ofMap ι).IsHomogeneous where
  norm0_smul_le c f := (eNorm_smul c f).le
  norm1_smul_le c f := by
    rcases eq_or_ne c 0 with rfl | hc
    · rw [zero_smul, isQuasiNormed_ofMap.norm1_zero]
      exact zero_le
    rw [ofMap_norm1 f, ENNReal.mul_iInf_of_ne (eNorm_ne_zero.2 hc) eNorm_ne_top]
    exact le_iInf fun y =>
      (norm1_ofMap_le (by rw [map_smul, y.2])).trans_eq (eNorm_smul _ _)

/-- **The couple of a bounded linear map is ordered**: `‖f‖ ≤ max(1, ‖ι‖) N₁(f)`, since
`‖ι y‖ ≤ ‖ι‖ ‖y‖`; the factor `max(1, ‖ι‖) ≥ 1` keeps the bound true for `ι = 0`, where
`N₁(f) = ∞` for `f ≠ 0`. -/
theorem norm0_ofMap_le (f : X) : (ofMap ι).norm0 f ≤ max 1 ‖ι‖ₑ * (ofMap ι).norm1 f := by
  rcases isEmpty_or_nonempty {y : Y // ι y = f} with hE | hN
  · rw [ofMap_norm1, iInf_of_empty, ENNReal.mul_top (one_pos.trans_le (le_max_left _ _)).ne']
    exact le_top
  · rw [ofMap_norm1, ENNReal.mul_iInf fun h =>
      absurd h (max_ne_top ENNReal.one_ne_top eNorm_ne_top)]
    refine le_iInf fun y => ?_
    calc (ofMap ι).norm0 f = ‖ι y‖ₑ := by rw [ofMap_norm0, y.2]
      _ ≤ ‖ι‖ₑ * ‖(y : Y)‖ₑ := ι.le_opENorm y
      _ ≤ max 1 ‖ι‖ₑ * ‖(y : Y)‖ₑ := by gcongr; exact le_max_right _ _

/-- **The K-functional of `ofMap ι`** is the K-functional `inf_y (‖f - ι y‖ + t ‖y‖)` of
`ApproximationSpaces.Interpolation.KFunctional`, for `0 < t < ∞`. -/
theorem kFunctional_ofMap (ht0 : t ≠ 0) (ht : t ≠ ∞) (f : X) :
    (ofMap ι).kFunctional t f = ApproximationScheme.kFunctional ι t f := by
  refine le_antisymm (le_iInf fun y => ?_) (le_iInf fun b => ?_)
  · exact (kFunctional_le (A := ofMap ι) (ι y) f).trans
      (add_le_add le_rfl (mul_le_mul_right (norm1_ofMap_le (ι := ι) rfl) t))
  · change _ ≤ ‖f - b‖ₑ + t * ⨅ y : {y : Y // ι y = b}, ‖(y : Y)‖ₑ
    rw [ENNReal.mul_iInf_of_ne ht0 ht, ENNReal.add_iInf]
    exact le_iInf fun y =>
      (ApproximationScheme.kFunctional_le (y : Y) f).trans_eq (by rw [y.2])

/-- The continuous K-norm of `ofMap ι` is `ApproximationScheme.kMethodNorm ι`. -/
theorem kMethodNorm_ofMap (f : X) :
    (ofMap ι).kMethodNorm θ q f = ApproximationScheme.kMethodNorm ι θ q f :=
  ApproximationScheme.phiFunctional_congr fun _ ht0 ht => kFunctional_ofMap ht0 ht f

/-- The real interpolation space of `ofMap ι` is that of
`ApproximationSpaces.Interpolation.KMethod`. -/
theorem memKMethod_ofMap_iff {f : X} :
    (ofMap ι).MemKMethod θ q f ↔ ApproximationScheme.MemKMethod ι θ q f := by
  rw [MemKMethod, kMethodNorm_ofMap]
  rfl

/-- The discrete K-norm of `ofMap ι` on the grid `2^(nρ)`, `n ∈ ℤ`, is
`ApproximationScheme.discreteKMethodNorm ι`. -/
theorem discreteKMethodNorm_ofMap (f : X) :
    (ofMap ι).discreteKMethodNorm θ ρ q f = ApproximationScheme.discreteKMethodNorm ι θ ρ q f := by
  rw [discreteKMethodNorm, ApproximationScheme.discreteKMethodNorm]
  congr 1
  funext n
  rw [discreteKSeq, ApproximationScheme.discreteKSeq,
    kFunctional_ofMap (ENNReal.rpow_pos two_pos ENNReal.ofNat_ne_top).ne'
      (ENNReal.two_rpow_ne_top _)]

/-- The norm of `ofMap ι` on the grid `2^(-kρ)`, `k ∈ ℕ`, is
`ApproximationScheme.interpNorm ι`. -/
theorem interpNorm_ofMap (f : X) :
    (ofMap ι).interpNorm θ ρ q f = ApproximationScheme.interpNorm ι θ ρ q f := by
  rw [interpNorm, ApproximationScheme.interpNorm, ofMap_norm0]
  congr 2
  funext k
  rw [ApproximationScheme.interpSeq,
    kFunctional_ofMap (ENNReal.dyadicWeight_ne_zero _ k) (ENNReal.dyadicWeight_ne_top _ k)]

end OfMap

end InterpCouple
