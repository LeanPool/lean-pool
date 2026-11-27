/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Decompositions.Blocks
public import LeanPool.FunctionSpaces.ApproximationSpaces.Nikolskii
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The trace theorem

A **trace bound** is a linear map `T : X → Y` that is controlled only on the approximants: it
maps `A n` into the sets `B n` of a scheme in `Y`, and

`‖T a‖_Y ≤ C n^β ‖a‖_X`   for `a ∈ A n`, `n ≥ 1`   (`ApproximationScheme.TraceBound`).

The restriction of functions to a hyperplane is the model: it is defined on continuous
functions, unbounded on `L_p`, and on trigonometric polynomials of degree `< n` it satisfies
the bound with `β = 1/p`.  The values of `T` away from the approximants play no role; a linear
map given only on `⋃ n, A n` extends to `X` by `LinearMap.exists_extend`
(`TraceBound.ofSubmodule`).

For `f ∈ A^β_1` the **trace** `TraceBound.ext f` is the limit of `T a_k` for near-best
approximants `a_k ∈ A (2^k)`.  It does not depend on the approximants
(`TraceBound.tendsto_ext`), agrees with `T` on the approximants (`TraceBound.ext_eq_of_mem`),
is linear (`TraceBound.extLinear`) and is bounded by the dyadic norm of `A^β_1`
(`TraceBound.enorm_ext_le`).

* **Transfer** (`TraceBound.approxNormDyadic_ext_le`): for `0 ≤ β < s` and `1 ≤ q ≤ ∞` the
  trace maps `A^s_q(X)` into `B^{s-β}_q(Y)`.  The proof ends with the transfer estimate
  (`approxNormDyadic_le_of_tail`) of the Nikolskii transfer theorem, which is the case
  `T = ι⁻¹` on the approximants.
* **Surjectivity** (`TraceBound.exists_ext_eq`): if every `b ∈ B (2^k)` is `T a` for some
  `a ∈ A (2^(k+γ))` with `‖a‖ ≤ C' 2^(-kβ) ‖b‖`, then every `g ∈ B^s_q(Y)`, `s > 0`, is the
  trace of some `f ∈ A^{s+β}_q(X)` with `‖f‖ ≲ ‖g‖`.  The proof lifts the blocks of the block
  decomposition of `g` (`ApproximationSpaces.Decompositions.Blocks`).
-/

@[expose] public section

open Filter Topology Finset
open scoped ENNReal

namespace ApproximationScheme

open ENNReal (lqNorm dyadicWeight)

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A **trace bound** of exponent `β` from the scheme `A` in `X` to the scheme `B` in `Y`: a
linear map `T` with `T (A n) ⊆ B n` and `‖T a‖ ≤ C n^β ‖a‖` for `a ∈ A n`, `n ≥ 1`.  Only the
values of `T` on the approximants matter. -/
structure TraceBound (A : ApproximationScheme X) (B : ApproximationScheme Y) (β : ℝ) where
  /-- The map on the approximants, extended linearly to `X`. -/
  T : X →ₗ[ℝ] Y
  mapsTo : ∀ n, ∀ a ∈ A n, T a ∈ B n
  /-- The constant of the trace inequality. -/
  C : ℝ≥0∞
  C_ne_top : C ≠ ∞
  bound : ∀ n : ℕ, 1 ≤ n → ∀ a ∈ A n, ‖T a‖ₑ ≤ C * (n : ℝ≥0∞) ^ β * ‖a‖ₑ

/-- The constant `2 C 4^β` by which the trace of a dyadic block exceeds `2^(kβ)` times its
error. -/
noncomputable def traceConst (C : ℝ≥0∞) (β : ℝ) : ℝ≥0∞ := 2 * C * dyadicWeight β 2

/-- The constant `2 C 4^β` is finite. -/
theorem traceConst_ne_top {C : ℝ≥0∞} (hC : C ≠ ∞) (β : ℝ) : traceConst C β ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hC) (ENNReal.dyadicWeight_ne_top β 2)

/-- The constant of the trace transfer theorem, `3 C + 3 K (1 - 2^(-(s-β)))⁻¹ + 2 K` with
`K = traceConst C β`. -/
noncomputable def traceTransferConst (C : ℝ≥0∞) (β s : ℝ) : ℝ≥0∞ :=
  3 * C + 3 * traceConst C β * (1 - (2 : ℝ≥0∞) ^ (-(s - β)))⁻¹ + 2 * traceConst C β

/-- The constant of the trace transfer theorem is finite for `β < s`. -/
theorem traceTransferConst_ne_top {C : ℝ≥0∞} (hC : C ≠ ∞) {β s : ℝ} (h : β < s) :
    traceTransferConst C β s ≠ ∞ := by
  have h1 := traceConst_ne_top hC β
  have h2 := ENNReal.one_sub_two_rpow_neg_inv_ne_top (sub_pos.2 h)
  unfold traceTransferConst
  exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
    ⟨ENNReal.mul_ne_top (by norm_num) hC,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) h1) h2⟩,
    ENNReal.mul_ne_top (by norm_num) h1⟩

/-- The constant of the trace surjectivity theorem,
`2 (1 - 2^(-(s+β)))⁻¹ 2^(γ(s+β)) C' (3·2^s + 4·4^s)`. -/
noncomputable def traceSurjConst (C' : ℝ≥0∞) (β s : ℝ) (γ : ℕ) : ℝ≥0∞ :=
  2 * (1 - (2 : ℝ≥0∞) ^ (-(s + β)))⁻¹ * dyadicWeight (s + β) γ * C' *
    (3 * 2 ^ s + 4 * dyadicWeight s 2)

/-- The constant of the trace surjectivity theorem is finite for `s + β > 0`. -/
theorem traceSurjConst_ne_top {C' : ℝ≥0∞} (hC' : C' ≠ ∞) {β s : ℝ} (h : 0 < s + β) (γ : ℕ) :
    traceSurjConst C' β s γ ≠ ∞ := by
  unfold traceSurjConst
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
    (by norm_num) (ENNReal.one_sub_two_rpow_neg_inv_ne_top h))
    (ENNReal.dyadicWeight_ne_top _ γ)) hC') (ENNReal.add_ne_top.2 ⟨?_, ?_⟩)
  · exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.two_rpow_ne_top _)
  · exact ENNReal.mul_ne_top (by norm_num) (ENNReal.dyadicWeight_ne_top s 2)

/-- The canonical near-best approximants with tolerances `2^(-k(β+1))`, used to define the
trace. -/
noncomputable def canonicalApprox (A : ApproximationScheme X) (β : ℝ) (f : X) :
    A.DyadicApprox f (dyadicWeight (-(β + 1))) :=
  (exists_dyadicApprox A f (fun k => ENNReal.dyadicWeight_ne_zero _ k)).some

/-- An approximant lies in the subspace spanned by all approximants. -/
theorem mem_iUnionSubmodule {A : ApproximationScheme X} {n : ℕ} {a : X} (ha : a ∈ A n) :
    a ∈ A.iUnionSubmodule := by
  rw [← SetLike.mem_coe, coe_iUnionSubmodule]
  exact Set.mem_iUnion.2 ⟨n, ha⟩

/-- For a dyadic approximation with `∑_k 2^(kβ) (E_{2^k}(f) + t_k) < ∞`, the weighted errors
`2^(kβ) ‖f - a_k‖` tend to `0`. -/
theorem DyadicApprox.tendsto_dyadicWeight_mul_enorm_sub {A : ApproximationScheme X} {f : X}
    {t : ℕ → ℝ≥0∞} (D : A.DyadicApprox f t) {β : ℝ}
    (hsum : ∑' k, dyadicWeight β k * (A.approxError f (2 ^ k) + t k) ≠ ∞) :
    Tendsto (fun k => dyadicWeight β k * ‖f - D.a k‖ₑ) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsum) (fun _ => bot_le)
    (fun k => by gcongr; exact D.eNorm_sub_le k)

/-- For `f ∈ A^β_1`, the series `∑_k 2^(kβ) (E_{2^k}(f) + 2^(-k(β+1)))` of the canonical
approximants is finite. -/
theorem tsum_canonical_ne_top {A : ApproximationScheme X} {β : ℝ} (hβ : 0 ≤ β) {f : X}
    (hf : A.MemApprox β 1 f) :
    ∑' k, dyadicWeight β k * (A.approxError f (2 ^ k) + dyadicWeight (-(β + 1)) k) ≠ ∞ := by
  have hL := (memApprox_iff_lqNorm_dyadic_lt_top le_rfl hβ).1 hf
  have h2 : ∀ k, dyadicWeight β k * dyadicWeight (-(β + 1)) k = dyadicWeight (-1) k :=
    fun k => by rw [← ENNReal.dyadicWeight_add]; congr 1; ring
  simp_rw [mul_add, h2]
  rw [tsum_add, ENNReal.tsum_dyadicWeight_neg_one, ← ENNReal.lqNorm_one]
  exact ENNReal.add_ne_top.2 ⟨hL.ne, by norm_num⟩

namespace TraceBound

variable {A : ApproximationScheme X} {B : ApproximationScheme Y} {β : ℝ} (TB : TraceBound A B β)

/-- A linear map defined on the span of the approximants, with `T (A n) ⊆ B n` and the trace
inequality, extends to a trace bound (`LinearMap.exists_extend`). -/
noncomputable def ofSubmodule (T₀ : A.iUnionSubmodule →ₗ[ℝ] Y)
    (hT : ∀ n (a : A.iUnionSubmodule), (a : X) ∈ A n → T₀ a ∈ B n) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hb : ∀ n : ℕ, 1 ≤ n → ∀ a : A.iUnionSubmodule, (a : X) ∈ A n →
      ‖T₀ a‖ₑ ≤ C * (n : ℝ≥0∞) ^ β * ‖(a : X)‖ₑ) : TraceBound A B β where
  T := (LinearMap.exists_extend T₀).choose
  mapsTo n a ha := by
    have h := LinearMap.congr_fun (LinearMap.exists_extend T₀).choose_spec
      ⟨a, mem_iUnionSubmodule ha⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h
    rw [h]
    exact hT n _ ha
  C := C
  C_ne_top := hC
  bound n hn a ha := by
    have h := LinearMap.congr_fun (LinearMap.exists_extend T₀).choose_spec
      ⟨a, mem_iUnionSubmodule ha⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h
    rw [h]
    exact hb n hn _ ha

/-- The trace of an extension agrees with the given map on the span of the approximants. -/
theorem ofSubmodule_T (T₀ : A.iUnionSubmodule →ₗ[ℝ] Y)
    (hT : ∀ n (a : A.iUnionSubmodule), (a : X) ∈ A n → T₀ a ∈ B n) (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hb : ∀ n : ℕ, 1 ≤ n → ∀ a : A.iUnionSubmodule, (a : X) ∈ A n →
      ‖T₀ a‖ₑ ≤ C * (n : ℝ≥0∞) ^ β * ‖(a : X)‖ₑ) (a : A.iUnionSubmodule) :
    (ofSubmodule T₀ hT C hC hb).T a = T₀ a := by
  have h := LinearMap.congr_fun (LinearMap.exists_extend T₀).choose_spec a
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h
  exact h

/-- The trace inequality on the dyadic levels: `‖T a‖ ≤ C 2^(kβ) ‖a‖` for `a ∈ A (2^k)`. -/
theorem enorm_apply_le {k : ℕ} {a : X} (ha : a ∈ A (2 ^ k)) :
    ‖TB.T a‖ₑ ≤ TB.C * dyadicWeight β k * ‖a‖ₑ := by
  have h := TB.bound (2 ^ k) Nat.one_le_two_pow a ha
  rwa [ENNReal.natCast_two_pow_rpow] at h

/-- The trace of a dyadic block: `‖T a_{k+1} - T a_k‖ ≤ 2 C 4^β 2^(kβ) (E_{2^k}(f) + t_k)`. -/
theorem enorm_apply_sub_succ_le {f : X} {t : ℕ → ℝ≥0∞} (D : A.DyadicApprox f t)
    (ht : Antitone t) (k : ℕ) :
    ‖TB.T (D.a (k + 1)) - TB.T (D.a k)‖ₑ ≤
      traceConst TB.C β * (dyadicWeight β k * (A.approxError f (2 ^ k) + t k)) := by
  rw [← map_sub]
  calc ‖TB.T (D.a (k + 1) - D.a k)‖ₑ ≤ TB.C * dyadicWeight β (k + 2) * ‖D.a (k + 1) - D.a k‖ₑ :=
        TB.enorm_apply_le (D.sub_mem k)
    _ ≤ TB.C * dyadicWeight β (k + 2) * (2 * (A.approxError f (2 ^ k) + t k)) := by
        gcongr; exact D.enorm_sub_succ_le ht k
    _ = _ := by simp only [traceConst, ENNReal.dyadicWeight_add_nat]; ring

/-- The traces of consecutive approximants are close: `edist (T a_k) (T a_{k+1})` is at most
`2 C 4^β 2^(kβ) (E_{2^k}(f) + t_k)`. -/
theorem edist_apply_succ_le {f : X} {t : ℕ → ℝ≥0∞} (D : A.DyadicApprox f t) (ht : Antitone t)
    (k : ℕ) :
    edist (TB.T (D.a k)) (TB.T (D.a (k + 1))) ≤
      traceConst TB.C β * (dyadicWeight β k * (A.approxError f (2 ^ k) + t k)) := by
  rw [edist_comm, eDist_eq_eNorm_sub]
  exact TB.enorm_apply_sub_succ_le D ht k

/-- The traces of near-best approximants form a Cauchy sequence when
`∑_k 2^(kβ) (E_{2^k}(f) + t_k) < ∞`. -/
theorem cauchySeq_apply {f : X} {t : ℕ → ℝ≥0∞} (D : A.DyadicApprox f t) (ht : Antitone t)
    (hsum : ∑' k, dyadicWeight β k * (A.approxError f (2 ^ k) + t k) ≠ ∞) :
    CauchySeq fun k => TB.T (D.a k) :=
  cauchySeq_of_edist_le_of_tsum_ne_top _ (TB.edist_apply_succ_le D ht) (by
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top (traceConst_ne_top TB.C_ne_top β) hsum)

/-- **Independence of the approximants**: if `c_k ∈ A (2^(k+γ))` and `c'_k ∈ A (2^(k+γ'))` both
satisfy `2^(kβ) ‖f - c_k‖ → 0`, then their traces are asymptotically equal. -/
theorem tendsto_edist_apply {f : X} {γ γ' : ℕ} {c c' : ℕ → X}
    (hc : ∀ k, c k ∈ A (2 ^ (k + γ))) (hc' : ∀ k, c' k ∈ A (2 ^ (k + γ')))
    (h : Tendsto (fun k => dyadicWeight β k * ‖f - c k‖ₑ) atTop (𝓝 0))
    (h' : Tendsto (fun k => dyadicWeight β k * ‖f - c' k‖ₑ) atTop (𝓝 0)) :
    Tendsto (fun k => edist (TB.T (c k)) (TB.T (c' k))) atTop (𝓝 0) := by
  set M := γ + γ' + 1
  have hmem : ∀ k, c k - c' k ∈ A (2 ^ (k + M)) := fun k => by
    refine A.mem_of_le ?_ (A.sub_mem (hc k) (hc' k))
    have h1 : 2 ^ (k + γ) ≤ 2 ^ (k + (γ + γ')) := Nat.pow_le_pow_right two_pos (by omega)
    have h2 : 2 ^ (k + γ') ≤ 2 ^ (k + (γ + γ')) := Nat.pow_le_pow_right two_pos (by omega)
    calc 2 ^ (k + γ) + 2 ^ (k + γ') ≤ 2 ^ (k + (γ + γ')) + 2 ^ (k + (γ + γ')) :=
          add_le_add h1 h2
      _ = 2 ^ (k + M) := by rw [show k + M = k + (γ + γ') + 1 by omega, pow_succ]; ring
  have hle : ∀ k, edist (TB.T (c k)) (TB.T (c' k)) ≤ TB.C * dyadicWeight β M *
      (dyadicWeight β k * ‖f - c k‖ₑ + dyadicWeight β k * ‖f - c' k‖ₑ) := fun k => by
    rw [eDist_eq_eNorm_sub, ← map_sub]
    calc ‖TB.T (c k - c' k)‖ₑ ≤ TB.C * dyadicWeight β (k + M) * ‖c k - c' k‖ₑ :=
          TB.enorm_apply_le (hmem k)
      _ ≤ TB.C * dyadicWeight β (k + M) * (‖f - c k‖ₑ + ‖f - c' k‖ₑ) := by
          gcongr
          calc ‖c k - c' k‖ₑ = ‖(f - c' k) - (f - c k)‖ₑ := by congr 1; abel
            _ ≤ ‖f - c' k‖ₑ + ‖f - c k‖ₑ := eNorm_sub_le
            _ = ‖f - c k‖ₑ + ‖f - c' k‖ₑ := add_comm _ _
      _ = _ := by rw [ENNReal.dyadicWeight_add_nat]; ring
  have hlim : Tendsto (fun k => TB.C * dyadicWeight β M *
      (dyadicWeight β k * ‖f - c k‖ₑ + dyadicWeight β k * ‖f - c' k‖ₑ)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (h.add h')
      (Or.inr (ENNReal.mul_ne_top TB.C_ne_top (ENNReal.dyadicWeight_ne_top β M)))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) hle

/-- The **trace** of `f`: the limit of `T a_k` for the canonical near-best approximants. -/
noncomputable def ext (f : X) : Y := limUnder atTop fun k => TB.T ((canonicalApprox A β f).a k)

/-- For `f ∈ A^β_1` the traces of the canonical approximants converge to the trace of `f`. -/
theorem tendsto_canonical [CompleteSpace Y] (hβ : 0 ≤ β) {f : X} (hf : A.MemApprox β 1 f) :
    Tendsto (fun k => TB.T ((canonicalApprox A β f).a k)) atTop (𝓝 (TB.ext f)) :=
  (TB.cauchySeq_apply _ (ENNReal.dyadicWeight_anti (by linarith))
    (tsum_canonical_ne_top hβ hf)).tendsto_limUnder

/-- **The trace is the limit for all approximants**: for `f ∈ A^β_1`, `c_k ∈ A (2^(k+γ))` and
`2^(kβ) ‖f - c_k‖ → 0`, the traces `T c_k` converge to the trace of `f`. -/
theorem tendsto_ext [CompleteSpace Y] (hβ : 0 ≤ β) {f : X} (hf : A.MemApprox β 1 f) {γ : ℕ}
    {c : ℕ → X} (hc : ∀ k, c k ∈ A (2 ^ (k + γ)))
    (hcf : Tendsto (fun k => dyadicWeight β k * ‖f - c k‖ₑ) atTop (𝓝 0)) :
    Tendsto (fun k => TB.T (c k)) atTop (𝓝 (TB.ext f)) := by
  set D := canonicalApprox A β f
  have hD := TB.tendsto_canonical hβ hf
  have hD0 := D.tendsto_dyadicWeight_mul_enorm_sub (tsum_canonical_ne_top hβ hf)
  have hed := TB.tendsto_edist_apply (γ' := 0) hc (fun k => by simpa using D.mem k) hcf hD0
  rw [tendsto_iff_edist_tendsto_0] at hD ⊢
  have := hed.add hD
  rw [add_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun _ => bot_le)
    fun k => edist_triangle _ _ _

/-- **The trace extends `T`**: on approximants the trace is `T`. -/
theorem ext_eq_of_mem [CompleteSpace Y] (hβ : 0 ≤ β) {m : ℕ} {a : X} (ha : a ∈ A m) :
    TB.ext a = TB.T a := by
  have hc : ∀ k, a ∈ A (2 ^ (k + m)) := fun k =>
    A.mem_of_le ((Nat.lt_two_pow_self).le.trans
      (Nat.pow_le_pow_right two_pos (Nat.le_add_left m k))) ha
  have h := TB.tendsto_ext hβ (memApprox_of_mem le_rfl hβ ha) hc (by simp)
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- The trace of `0` is `0`. -/
theorem ext_zero [CompleteSpace Y] (hβ : 0 ≤ β) : TB.ext 0 = 0 := by
  rw [TB.ext_eq_of_mem hβ (A.zero_mem 0), map_zero]

/-- The trace is additive on `A^β_1`. -/
theorem ext_add [CompleteSpace Y] (hβ : 0 ≤ β) {f g : X} (hf : A.MemApprox β 1 f)
    (hg : A.MemApprox β 1 g) : TB.ext (f + g) = TB.ext f + TB.ext g := by
  set Df := canonicalApprox A β f
  set Dg := canonicalApprox A β g
  have hcf := Df.tendsto_dyadicWeight_mul_enorm_sub (tsum_canonical_ne_top hβ hf)
  have hcg := Dg.tendsto_dyadicWeight_mul_enorm_sub (tsum_canonical_ne_top hβ hg)
  have hc : ∀ k, Df.a k + Dg.a k ∈ A (2 ^ (k + 1)) := fun k =>
    add_mem_pow_succ (Df.mem k) (Dg.mem k)
  have hlim : Tendsto (fun k => dyadicWeight β k * ‖(f + g) - (Df.a k + Dg.a k)‖ₑ) atTop
      (𝓝 0) := by
    have := hcf.add hcg
    rw [add_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun _ => bot_le)
      fun k => ?_
    calc dyadicWeight β k * ‖(f + g) - (Df.a k + Dg.a k)‖ₑ
        = dyadicWeight β k * ‖(f - Df.a k) + (g - Dg.a k)‖ₑ := by congr 2; abel
      _ ≤ dyadicWeight β k * (‖f - Df.a k‖ₑ + ‖g - Dg.a k‖ₑ) := by
          gcongr; exact eNorm_add_le _ _
      _ = _ := mul_add _ _ _
  have h1 := TB.tendsto_ext hβ (MemApprox.add le_rfl hβ hf hg) hc hlim
  have h2 : Tendsto (fun k => TB.T (Df.a k + Dg.a k)) atTop (𝓝 (TB.ext f + TB.ext g)) := by
    simp_rw [map_add]
    exact (TB.tendsto_canonical hβ hf).add (TB.tendsto_canonical hβ hg)
  exact tendsto_nhds_unique h1 h2

/-- The trace is homogeneous on `A^β_1`. -/
theorem ext_smul [CompleteSpace Y] (hβ : 0 ≤ β) {f : X} (hf : A.MemApprox β 1 f) (r : ℝ) :
    TB.ext (r • f) = r • TB.ext f := by
  set D := canonicalApprox A β f
  have hcf := D.tendsto_dyadicWeight_mul_enorm_sub (tsum_canonical_ne_top hβ hf)
  have hc : ∀ k, r • D.a k ∈ A (2 ^ (k + 0)) := fun k => A.smul_mem r (D.mem k)
  have hlim : Tendsto (fun k => dyadicWeight β k * ‖r • f - r • D.a k‖ₑ) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ‖r‖ₑ) hcf (Or.inr eNorm_ne_top)
    rw [mul_zero] at this
    refine this.congr fun k => ?_
    rw [← smul_sub, eNorm_smul]; ring
  have h1 := TB.tendsto_ext hβ (hf.smul r) hc hlim
  have h2 : Tendsto (fun k => TB.T (r • D.a k)) atTop (𝓝 (r • TB.ext f)) := by
    simp_rw [map_smul]
    exact (TB.tendsto_canonical hβ hf).const_smul r
  exact tendsto_nhds_unique h1 h2

/-- The trace as a linear map on `A^β_1`. -/
noncomputable def extLinear [CompleteSpace Y] (hβ : 0 ≤ β) :
    A.approxSpace β 1 hβ le_rfl →ₗ[ℝ] Y where
  toFun f := TB.ext f
  map_add' f g := TB.ext_add hβ (mem_approxSpace.1 f.2) (mem_approxSpace.1 g.2)
  map_smul' r f := TB.ext_smul hβ (mem_approxSpace.1 f.2) r

/-- **The distance of a traced approximant to the trace**: for near-best approximants with
decreasing tolerances and `∑_k 2^(kβ) (E_{2^k}(f) + t_k) < ∞`,
`edist (T a_k) (ext f) ≤ 2 C 4^β ∑_{i ≥ 0} 2^((k+i)β) (E_{2^(k+i)}(f) + t_{k+i})`. -/
theorem edist_apply_ext_le [CompleteSpace Y] (hβ : 0 ≤ β) {f : X} {t : ℕ → ℝ≥0∞}
    (D : A.DyadicApprox f t) (ht : Antitone t)
    (hsum : ∑' k, dyadicWeight β k * (A.approxError f (2 ^ k) + t k) ≠ ∞) (k : ℕ) :
    edist (TB.T (D.a k)) (TB.ext f) ≤ traceConst TB.C β *
      ∑' i, dyadicWeight β (k + i) * (A.approxError f (2 ^ (k + i)) + t (k + i)) := by
  have hf : A.MemApprox β 1 f := by
    refine (memApprox_iff_lqNorm_dyadic_lt_top le_rfl hβ).2 (lt_of_le_of_lt ?_ hsum.lt_top)
    rw [ENNReal.lqNorm_one]
    exact tsum_le_tsum fun k => by rw [approxSeqDyadic]; gcongr; exact le_self_add
  have hlim := TB.tendsto_ext hβ hf (γ := 0) (fun k => by simpa using D.mem k)
    (D.tendsto_dyadicWeight_mul_enorm_sub hsum)
  calc edist (TB.T (D.a k)) (TB.ext f) ≤ ∑' m, traceConst TB.C β *
        (dyadicWeight β (k + m) * (A.approxError f (2 ^ (k + m)) + t (k + m))) :=
        edist_le_tsum_of_edist_le_of_tendsto _ (TB.edist_apply_succ_le D ht) hlim k
    _ = _ := ENNReal.tsum_mul_left

/-- The norm of the trace through any near-best approximants:
`‖ext f‖ ≤ C (2 ‖f‖ + t_0) + 2 C 4^β ∑_k 2^(kβ) (E_{2^k}(f) + t_k)`. -/
theorem enorm_ext_le_of_dyadicApprox [CompleteSpace Y] (hβ : 0 ≤ β) {f : X} {t : ℕ → ℝ≥0∞}
    (D : A.DyadicApprox f t) (ht : Antitone t)
    (hsum : ∑' k, dyadicWeight β k * (A.approxError f (2 ^ k) + t k) ≠ ∞) :
    ‖TB.ext f‖ₑ ≤ TB.C * (2 * ‖f‖ₑ + t 0) +
      traceConst TB.C β * ∑' k, dyadicWeight β k * (A.approxError f (2 ^ k) + t k) := by
  have h0 := TB.edist_apply_ext_le hβ D ht hsum 0
  simp only [zero_add] at h0
  have hT0 : ‖TB.T (D.a 0)‖ₑ ≤ TB.C * (2 * ‖f‖ₑ + t 0) := by
    calc ‖TB.T (D.a 0)‖ₑ ≤ TB.C * dyadicWeight β 0 * ‖D.a 0‖ₑ := TB.enorm_apply_le (D.mem 0)
      _ ≤ TB.C * (2 * ‖f‖ₑ + t 0) := by
          rw [ENNReal.dyadicWeight_zero_right, mul_one]; gcongr; exact D.enorm_zero_le
  calc ‖TB.ext f‖ₑ = ‖TB.T (D.a 0) + (TB.ext f - TB.T (D.a 0))‖ₑ := by congr 1; abel
    _ ≤ ‖TB.T (D.a 0)‖ₑ + ‖TB.ext f - TB.T (D.a 0)‖ₑ := eNorm_add_le _ _
    _ ≤ _ := by
        gcongr
        rw [← eDist_eq_eNorm_sub, edist_comm]
        exact h0

/-- **The trace is bounded on `A^β_1`**:
`‖ext f‖ ≤ (3 C + 3·2 C 4^β) (‖f‖ + ∑_k 2^(kβ) E_{2^k}(f))`. -/
theorem enorm_ext_le [CompleteSpace Y] (hβ : 0 ≤ β) {f : X} (hf : A.MemApprox β 1 f) :
    ‖TB.ext f‖ₑ ≤ (3 * TB.C + 3 * traceConst TB.C β) * A.approxNormDyadic β 1 f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [TB.ext_zero hβ, eNorm_zero]; exact bot_le
  obtain ⟨D⟩ := exists_dyadicApprox A f (tolerance_ne_zero hf0 β)
  have h := TB.enorm_ext_le_of_dyadicApprox hβ D (tolerance_anti f hβ)
    (tsum_dyadicWeight_mul_add_tolerance_ne_top le_rfl
      ((memApprox_iff_lqNorm_dyadic_lt_top le_rfl hβ).1 hf).ne)
  rw [tolerance_zero] at h
  exact h.trans (mul_add_mul_tsum_tolerance_le _ _ f β)

/-- **The trace transfer theorem**: for `0 ≤ β < s` and `1 ≤ q ≤ ∞` the trace maps `A^s_q(X)`
into `B^{s-β}_q(Y)`, with `‖ext f‖_{B^{s-β}_q} ≤ K ‖f‖_{A^s_q}` in the dyadic quasi-norms,
`K = traceTransferConst C β s`. -/
theorem approxNormDyadic_ext_le [CompleteSpace Y] (hβ : 0 ≤ β) {s : ℝ} (hβs : β < s)
    {q : ℝ≥0∞} (hq : 1 ≤ q) {f : X} (hf : A.MemApprox s q f) :
    B.approxNormDyadic (s - β) q (TB.ext f) ≤
      traceTransferConst TB.C β s * A.approxNormDyadic s q f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [TB.ext_zero hβ, approxNormDyadic_zero]; exact bot_le
  obtain ⟨D⟩ := exists_dyadicApprox A f (tolerance_ne_zero hf0 s)
  have ht := tolerance_anti f (hβ.trans hβs.le)
  have hsum := tsum_dyadicWeight_mul_add_tolerance_ne_top hβs.le (hf.lqNorm_one_lt_top hq hβ hβs).ne
  have hy := TB.enorm_ext_le_of_dyadicApprox hβ D ht hsum
  rw [tolerance_zero] at hy
  refine approxNormDyadic_le_of_tail hβs.le hq f hy fun k => ?_
  refine (approxError_le_of_mem (TB.mapsTo _ _ (D.mem k)) _).trans ?_
  rw [← eDist_eq_eNorm_sub, edist_comm]
  exact TB.edist_apply_ext_le hβ D ht hsum k

/-- **The trace transfer theorem**, membership form: `f ∈ A^s_q(X)` gives
`ext f ∈ B^{s-β}_q(Y)` for `0 ≤ β < s`. -/
theorem memApprox_ext [CompleteSpace Y] (hβ : 0 ≤ β) {s : ℝ} (hβs : β < s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {f : X} (hf : A.MemApprox s q f) : B.MemApprox (s - β) q (TB.ext f) := by
  refine (memApprox_iff_approxNormDyadic_lt_top hq (sub_nonneg.2 hβs.le)).2 ?_
  exact (TB.approxNormDyadic_ext_le hβ hβs hq hf).trans_lt (ENNReal.mul_lt_top
    (traceTransferConst_ne_top TB.C_ne_top hβs).lt_top
    ((memApprox_iff_approxNormDyadic_lt_top hq (hβ.trans hβs.le)).1 hf))

/-- A **right inverse bound** for a trace: every `b ∈ B (2^k)` is `T a` for some
`a ∈ A (2^(k+γ))` with `‖a‖ ≤ C' 2^(-kβ) ‖b‖`.  For the restriction to a hyperplane, `a` is
`b` times a peaked function of width `2^(-k)` in the normal direction. -/
def RightInverseBound (γ : ℕ) (C' : ℝ≥0∞) : Prop :=
  ∀ k, ∀ b ∈ B (2 ^ k), ∃ a ∈ A (2 ^ (k + γ)), TB.T a = b ∧
    ‖a‖ₑ ≤ C' * dyadicWeight (-β) k * ‖b‖ₑ

/-- **The trace of a lifted series**: if `a_j ∈ A_{2^(j+γ)}` lift `b_j = T a_j` with
`‖a_j‖ ≤ C' 2^(-jβ) ‖b_j‖`, `∑ ‖b_j‖ < ∞` and `∑ b_j = g`, and `f = ∑ a_j` lies in `A^β_1`, then
the trace of `f` is `g`. The partial sums of the moved series approximate `f` with
`2^(Kβ) ‖f - ∑_{i < K+γ} G_i‖ ≤ C' ∑_m ‖b_{m+K}‖ → 0`, and `TraceBound.tendsto_ext` applies. -/
theorem ext_eq_of_hasSum_lift [CompleteSpace Y] (hβ : 0 ≤ β) {γ : ℕ} {C' : ℝ≥0∞} (hC' : C' ≠ ∞)
    {a : ℕ → X} {b : ℕ → Y} (ha : ∀ j, a j ∈ A (2 ^ (j + γ))) (hTa : ∀ j, TB.T (a j) = b j)
    (hale : ∀ j, ‖a j‖ₑ ≤ C' * dyadicWeight (-β) j * ‖b j‖ₑ) (hb_fin : ∑' j, ‖b j‖ₑ ≠ ∞)
    {g : Y} (hb_sum : HasSum b g) {f : X} (hfa : HasSum a f) (hfβ : A.MemApprox β 1 f) :
    TB.ext f = g := by
  have hw1 : ∀ j, dyadicWeight (-β) j ≤ 1 := fun j =>
    (ENNReal.dyadicWeight_le_of_le (by linarith) j).trans_eq (ENNReal.dyadicWeight_zero_left j)
  have hG : HasSum (shiftSeq γ a) f := hasSum_shiftSeq hfa
  have htailG : ∀ K, ‖f - ∑ i ∈ range (K + γ), shiftSeq γ a i‖ₑ ≤ ∑' m, ‖a (m + K)‖ₑ :=
    fun K => (hG.enorm_sub_sum_range_le (K + γ)).trans_eq (by
      congr 1; funext m; rw [← add_assoc, shiftSeq_add])
  have hdecay : ∀ K, dyadicWeight β K * ‖f - ∑ i ∈ range (K + γ), shiftSeq γ a i‖ₑ ≤
      C' * ∑' m, ‖b (m + K)‖ₑ := fun K => by
    calc dyadicWeight β K * ‖f - ∑ i ∈ range (K + γ), shiftSeq γ a i‖ₑ
        ≤ dyadicWeight β K * ∑' m, ‖a (m + K)‖ₑ := mul_le_mul' le_rfl (htailG K)
      _ ≤ dyadicWeight β K * ∑' m, C' * dyadicWeight (-β) (m + K) * ‖b (m + K)‖ₑ :=
          mul_le_mul' le_rfl (tsum_le_tsum fun m => hale (m + K))
      _ = ∑' m, C' * dyadicWeight (-β) m * ‖b (m + K)‖ₑ := by
          rw [← ENNReal.tsum_mul_left]
          congr 1; funext m
          rw [ENNReal.dyadicWeight_add_nat]
          calc dyadicWeight β K * (C' * (dyadicWeight (-β) m * dyadicWeight (-β) K) *
                ‖b (m + K)‖ₑ)
              = C' * dyadicWeight (-β) m * ‖b (m + K)‖ₑ *
                  (dyadicWeight β K * dyadicWeight (-β) K) := by ring
            _ = _ := by rw [ENNReal.dyadicWeight_mul_neg_self, mul_one]
      _ ≤ ∑' m, C' * ‖b (m + K)‖ₑ := tsum_le_tsum fun m => by
          calc C' * dyadicWeight (-β) m * ‖b (m + K)‖ₑ ≤ C' * 1 * ‖b (m + K)‖ₑ := by
                gcongr; exact hw1 m
            _ = C' * ‖b (m + K)‖ₑ := by rw [mul_one]
      _ = C' * ∑' m, ‖b (m + K)‖ₑ := ENNReal.tsum_mul_left
  have hcf : Tendsto (fun K => dyadicWeight β K * ‖f - ∑ i ∈ range (K + γ), shiftSeq γ a i‖ₑ)
      atTop (𝓝 0) := by
    have h0 := ENNReal.Tendsto.const_mul (a := C')
      (ENNReal.tendsto_sum_nat_add (fun j => ‖b j‖ₑ) hb_fin) (Or.inr hC')
    rw [mul_zero] at h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => bot_le) hdecay
  have h1 := TB.tendsto_ext hβ hfβ (c := fun K => ∑ i ∈ range (K + γ), shiftSeq γ a i)
    (fun K => sum_range_mem (shiftSeq_mem ha) (K + γ)) hcf
  have hTG : HasSum (fun i => TB.T (shiftSeq γ a i)) g := by
    refine (hasSum_nat_add_iff' γ).1 ?_
    have h1' : (fun n => TB.T (shiftSeq γ a (n + γ))) = b :=
      funext fun n => by rw [shiftSeq_add, hTa]
    have h2' : ∑ i ∈ range γ, TB.T (shiftSeq γ a i) = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [shiftSeq_of_lt a (Finset.mem_range.1 hi), map_zero]
    rw [h1', h2', sub_zero]; exact hb_sum
  have h2 : Tendsto (fun K => TB.T (∑ i ∈ range (K + γ), shiftSeq γ a i)) atTop (𝓝 g) := by
    simp_rw [map_sum]
    exact hTG.tendsto_sum_nat.comp (tendsto_add_atTop_nat γ)
  exact tendsto_nhds_unique h1 h2

/-- **Surjectivity of the trace**: in Banach spaces, for `β ≥ 0`, a right inverse bound,
`s > 0` and `1 ≤ q ≤ ∞`, every `g ∈ B^s_q(Y)` is the trace of some `f ∈ A^{s+β}_q(X)` with
`‖f‖_{A^{s+β}_q} ≤ K ‖g‖_{B^s_q}` in the dyadic quasi-norms, `K = traceSurjConst C' β s γ`.
The proof lifts the blocks `b_j ∈ B (2^j)` of a block decomposition of `g`
(`ApproximationScheme.exists_blocks`) to `a_j` with `T a_j = b_j` and takes `f = ∑ a_j`. -/
theorem exists_ext_eq [CompleteSpace X] [CompleteSpace Y] (hβ : 0 ≤ β) {γ : ℕ} {C' : ℝ≥0∞}
    (hC' : C' ≠ ∞) (hR : TB.RightInverseBound γ C') {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞}
    (hq : 1 ≤ q) {g : Y} (hg : B.MemApprox s q g) :
    ∃ f : X, A.MemApprox (s + β) q f ∧ TB.ext f = g ∧
      A.approxNormDyadic (s + β) q f ≤ traceSurjConst C' β s γ * B.approxNormDyadic s q g := by
  have hsβ : 0 < s + β := by linarith
  have hw1 : ∀ j, dyadicWeight (-β) j ≤ 1 := fun j =>
    (ENNReal.dyadicWeight_le_of_le (by linarith) j).trans_eq (ENNReal.dyadicWeight_zero_left j)
  -- the blocks of `g`, and their lifts
  obtain ⟨b, hb_mem, hb_sum, hb_fin, hlqb⟩ := B.exists_blocks hs hq hg
  set N := B.approxNormDyadic s q g
  choose a ha hTa hale using fun j => hR j (b j) (hb_mem j)
  have hale' : ∀ j, ‖a j‖ₑ ≤ C' * ‖b j‖ₑ := fun j => by
    calc ‖a j‖ₑ ≤ C' * dyadicWeight (-β) j * ‖b j‖ₑ := hale j
      _ ≤ C' * 1 * ‖b j‖ₑ := by gcongr; exact hw1 j
      _ = C' * ‖b j‖ₑ := by rw [mul_one]
  have ha_fin : ∑' j, ‖a j‖ₑ ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top hC' hb_fin)
    ((tsum_le_tsum hale').trans_eq ENNReal.tsum_mul_left)
  have ha_summ : Summable a := Summable.of_eNorm ha_fin
  set f := ∑' j, a j
  have hfa : HasSum a f := ha_summ.hasSum
  -- the norm of `f`, through the lifted blocks placed at the levels `j + γ`
  have hpt : ∀ j, dyadicWeight (s + β) (j + γ) * ‖a j‖ₑ ≤
      dyadicWeight (s + β) γ * C' * (dyadicWeight s j * ‖b j‖ₑ) := fun j => by
    calc dyadicWeight (s + β) (j + γ) * ‖a j‖ₑ
        ≤ dyadicWeight (s + β) (j + γ) * (C' * dyadicWeight (-β) j * ‖b j‖ₑ) := by
          gcongr; exact hale j
      _ = dyadicWeight (s + β) γ * C' *
            ((dyadicWeight (s + β) j * dyadicWeight (-β) j) * ‖b j‖ₑ) := by
          rw [ENNReal.dyadicWeight_add_nat]; ring
      _ = dyadicWeight (s + β) γ * C' * (dyadicWeight s j * ‖b j‖ₑ) := by
          rw [← ENNReal.dyadicWeight_add, show s + β + -β = s by ring]
  have hnorm : A.approxNormDyadic (s + β) q f ≤ traceSurjConst C' β s γ * N := by
    calc A.approxNormDyadic (s + β) q f
        ≤ 2 * (1 - (2 : ℝ≥0∞) ^ (-(s + β)))⁻¹ *
            lqNorm q (fun i => dyadicWeight (s + β) i * ‖shiftSeq γ a i‖ₑ) :=
          approxNormDyadic_le_of_hasSum hq (shiftSeq_mem ha) (hasSum_shiftSeq hfa)
      _ ≤ 2 * (1 - (2 : ℝ≥0∞) ^ (-(s + β)))⁻¹ *
            (dyadicWeight (s + β) γ * C' * ((3 * 2 ^ s + 4 * dyadicWeight s 2) * N)) := by
          gcongr
          calc _ ≤ lqNorm q (fun j => dyadicWeight (s + β) (j + γ) * ‖a j‖ₑ) :=
                lqNorm_shiftSeq_le γ a (s + β) q
            _ ≤ lqNorm q (fun j => dyadicWeight (s + β) γ * C' * (dyadicWeight s j * ‖b j‖ₑ)) :=
                ENNReal.lqNorm_mono hpt
            _ = dyadicWeight (s + β) γ * C' * lqNorm q (fun j => dyadicWeight s j * ‖b j‖ₑ) :=
                ENNReal.lqNorm_const_mul _ _
            _ ≤ _ := by gcongr
      _ = traceSurjConst C' β s γ * N := by simp only [traceSurjConst]; ring
  have hfmem : A.MemApprox (s + β) q f := (memApprox_iff_approxNormDyadic_lt_top hq hsβ.le).2
    (hnorm.trans_lt (ENNReal.mul_lt_top (traceSurjConst_ne_top hC' hsβ γ).lt_top
      ((memApprox_iff_approxNormDyadic_lt_top hq hs.le).1 hg)))
  -- the trace of `f` is `g`
  exact ⟨f, hfmem, TB.ext_eq_of_hasSum_lift hβ hC' ha hTa hale hb_fin hb_sum hfa
    (hfmem.mono hq le_rfl hβ (Or.inl (by linarith))), hnorm⟩

end TraceBound

end ApproximationScheme
