/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Scheme
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The error of best approximation

For an approximation scheme `A` in a normed space `X`, the **error of best approximation** of
`f ∈ X` from `A n` is

`E_n(f) = inf { ‖f - a‖ : a ∈ A n }`,

in Lean `A.approxError f n`, defined as the extended distance `Metric.infEDist f (A n)` with
values in `ℝ≥0∞`; it is finite (`approxError_ne_top`).  This file collects its calculus:
`E_0(f) = ‖f‖`, `E_n(f) ≤ ‖f‖`, `E_n` decreases in `n`, the bounds `r ≤ E_n(f)` and
`r ≤ E_n(f)²` through all approximants, `E_n(c f) = |c| E_n(f)`,
`E_{m+n}(f + g) ≤ E_m(f) + E_n(g)`, `E_n(f) ≤ E_n(g) + ‖f - g‖`, `E_n(f) → 0` exactly for `f`
in the closure of `⋃ A n`, a bounded linear map `T` with `T (A n) ⊆ B n` satisfies
`E^B_n(T f) ≤ ‖T‖ E^A_n(f)`, and bounds by a subadditive modulus pass from a dense set to all
of `X`.  The Lebesgue inequality `‖f - P f‖ ≤ (1 + C) ‖f - a‖` holds for every additive map `P`
with `‖P x‖ ≤ C ‖x‖` that fixes `a`.

A best approximant need not exist, since the sets `A n` need not be closed (sets of `n`-term
approximants are in general not closed).  Proofs pick approximants `a ∈ A n` with
`‖f - a‖ ≤ E_n(f) + ε` (`ApproximationScheme.exists_mem_enorm_sub_le_add`), or bound `E_n(f)`
through every approximant at once (`ApproximationScheme.le_mul_approxError_of_forall_mem`).
-/

@[expose] public section

open Filter Topology
open scoped ENNReal

namespace ApproximationScheme

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

variable (A : ApproximationScheme X)

/-- The **error of best approximation** `E_n(f) = inf_{a ∈ A n} ‖f - a‖ ∈ [0, ∞]` of `f` from
the approximants of complexity `n`, the extended distance from `f` to `A n`. -/
noncomputable def approxError (f : X) (n : ℕ) : ℝ≥0∞ := Metric.infEDist f (A n)

variable {A}

/-- The errors are finite, since `A n` is nonempty. -/
theorem approxError_ne_top (f : X) (n : ℕ) : A.approxError f n ≠ ∞ :=
  Metric.infEDist_ne_top (A.nonempty n)

/-- Every approximant gives an upper bound: `E_n(f) ≤ ‖f - a‖` for `a ∈ A_n`. -/
theorem approxError_le_of_mem {n : ℕ} {a : X} (ha : a ∈ A n) (f : X) :
    A.approxError f n ≤ ‖f - a‖ₑ := by
  rw [← eDist_eq_eNorm_sub]; exact Metric.infEDist_le_edist_of_mem ha

/-- The error never exceeds the norm, since `0` is an approximant. -/
theorem approxError_le_enorm (f : X) (n : ℕ) : A.approxError f n ≤ ‖f‖ₑ := by
  simpa using approxError_le_of_mem (A.zero_mem n) f

/-- `E_n(0) = 0`. -/
@[simp]
theorem approxError_zero_left (n : ℕ) : A.approxError 0 n = 0 :=
  Metric.infEDist_zero_of_mem (A.zero_mem n)

/-- `E_0(f) = ‖f‖`, because `A 0 = {0}`. -/
@[simp]
theorem approxError_zero_right (f : X) : A.approxError f 0 = ‖f‖ₑ := by
  simp [approxError, A.coe_zero, Metric.infEDist_singleton]

/-- `E_n(f) = 0` for `f ∈ A_n`. -/
theorem approxError_eq_zero_of_mem {n : ℕ} {f : X} (hf : f ∈ A n) : A.approxError f n = 0 :=
  Metric.infEDist_zero_of_mem hf

/-- `E_n(f) = 0` for `f` in the closure of `A_n`. -/
theorem approxError_eq_zero_of_mem_closure {n : ℕ} {f : X} (hf : f ∈ closure (A n)) :
    A.approxError f n = 0 :=
  Metric.mem_closure_iff_infEDist_zero.1 hf

/-- The error decreases as the complexity grows. -/
theorem approxError_anti (f : X) : Antitone (A.approxError f) := fun _ _ h =>
  Metric.infEDist_anti (A.mono h)

/-- A scheme with larger sets has smaller errors. -/
theorem approxError_anti_scheme {A' : ApproximationScheme X} (h : ∀ n, A n ⊆ A' n) (f : X)
    (n : ℕ) : A'.approxError f n ≤ A.approxError f n :=
  Metric.infEDist_anti (h n)

/-- `r ≤ E_n(f)` iff `r ≤ ‖f - a‖` for every `a ∈ A_n`. -/
theorem le_approxError_iff {n : ℕ} {f : X} {r : ℝ≥0∞} :
    r ≤ A.approxError f n ↔ ∀ a ∈ A n, r ≤ ‖f - a‖ₑ := by
  simp only [approxError, Metric.le_infEDist, eDist_eq_eNorm_sub]

/-- `r ≤ E_n(f)²` iff `r ≤ ‖f - a‖²` for every `a ∈ A_n`. Squaring preserves the order of
`[0, ∞]` (`ENNReal.rpow_inv_le_iff`), so `le_approxError_iff` applies to `r^(1/2)`. -/
theorem le_approxError_sq_iff {n : ℕ} {f : X} {r : ℝ≥0∞} :
    r ≤ A.approxError f n ^ 2 ↔ ∀ a ∈ A n, r ≤ ‖f - a‖ₑ ^ 2 := by
  have h2 : (0 : ℝ) < 2 := two_pos
  simp_rw [← ENNReal.rpow_two, ← ENNReal.rpow_inv_le_iff h2]
  exact le_approxError_iff

/-- If the error is below `r`, some approximant is closer than `r`. -/
theorem exists_mem_enorm_sub_lt {n : ℕ} {f : X} {r : ℝ≥0∞} (h : A.approxError f n < r) :
    ∃ a ∈ A n, ‖f - a‖ₑ < r := by
  simpa [eDist_eq_eNorm_sub] using Metric.infEDist_lt_iff.1 h

/-- **Near-best approximants.** For every `ε > 0` there is `a ∈ A n` with
`‖f - a‖ ≤ E_n(f) + ε`.  A best approximant (`ε = 0`) need not exist. -/
theorem exists_mem_enorm_sub_le_add (n : ℕ) (f : X) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ a ∈ A n, ‖f - a‖ₑ ≤ A.approxError f n + ε := by
  obtain ⟨a, ha, h⟩ := exists_mem_enorm_sub_lt (ENNReal.lt_add_right (approxError_ne_top f n) hε)
  exact ⟨a, ha, h.le⟩

/-- To bound a quantity by `C · E_n(f)` with `C < ∞` it suffices to bound it by `C ‖f - a‖`
for every approximant `a`.  The finiteness of `C` is needed: for `C = ∞` and `f` in the
closure of `A n` outside `A n`, every `C ‖f - a‖` is `∞`, so the hypothesis holds for every
`e`, while `C · E_n(f) = ∞ · 0 = 0`. -/
theorem le_mul_approxError_of_forall_mem {n : ℕ} {f : X} {e C : ℝ≥0∞} (hC : C ≠ ∞)
    (h : ∀ a ∈ A n, e ≤ C * ‖f - a‖ₑ) : e ≤ C * A.approxError f n := by
  rcases eq_or_ne C 0 with rfl | hC0
  · simpa using h 0 (A.zero_mem n)
  rw [mul_comm, ← ENNReal.div_le_iff hC0 hC, le_approxError_iff]
  exact fun a ha => (ENNReal.div_le_iff hC0 hC).2 (by rw [mul_comm]; exact h a ha)

/-- **Subadditivity** for any three complexities with `A m + A n ⊆ A k`:
`E_k(f + g) ≤ E_m(f) + E_n(g)`. -/
theorem approxError_add_le_of_add_mem {m n k : ℕ} (h : ∀ a ∈ A m, ∀ b ∈ A n, a + b ∈ A k)
    (f g : X) : A.approxError (f + g) k ≤ A.approxError f m + A.approxError g n := by
  refine ENNReal.le_iInf₂_add_iInf₂ fun a ha b hb => ?_
  calc A.approxError (f + g) k ≤ edist (f + g) (a + b) :=
        Metric.infEDist_le_edist_of_mem (h a ha b hb)
    _ ≤ edist f a + edist g b := edist_add_add_le f g a b

/-- **Subadditivity**: `E_{m+n}(f + g) ≤ E_m(f) + E_n(g)`, because `A m + A n ⊆ A (m + n)`. -/
theorem approxError_add_le (m n : ℕ) (f g : X) :
    A.approxError (f + g) (m + n) ≤ A.approxError f m + A.approxError g n :=
  approxError_add_le_of_add_mem (fun _ ha _ hb => add_mem ha hb) f g

/-- The dyadic form of subadditivity: `E_{2^(k+1)}(f + g) ≤ E_{2^k}(f) + E_{2^k}(g)`. -/
theorem approxError_add_le_pow_succ (k : ℕ) (f g : X) :
    A.approxError (f + g) (2 ^ (k + 1)) ≤ A.approxError f (2 ^ k) + A.approxError g (2 ^ k) :=
  approxError_add_le_of_add_mem (fun _ ha _ hb => A.add_mem_pow_succ ha hb) f g

/-- **Homogeneity**: `E_n(c f) = |c| E_n(f)`, because `c • A n = A n` for `c ≠ 0`. -/
theorem approxError_smul (c : ℝ) (f : X) (n : ℕ) :
    A.approxError (c • f) n = ‖c‖ₑ * A.approxError f n := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have := infEDist_smul₀ hc (A n) f
    rw [A.smul_set_eq hc n, ENNReal.smul_def, smul_eq_mul] at this
    exact this

/-- `E_n(-f) = E_n(f)`. -/
@[simp]
theorem approxError_neg (f : X) (n : ℕ) : A.approxError (-f) n = A.approxError f n := by
  simpa using approxError_smul (A := A) (-1) f n

/-- `E_n(f) ≤ E_n(g) + ‖f - g‖`: the error is `1`-Lipschitz in `f`. -/
theorem approxError_le_approxError_add_enorm (n : ℕ) (f g : X) :
    A.approxError f n ≤ A.approxError g n + ‖f - g‖ₑ := by
  rw [← eDist_eq_eNorm_sub]; exact Metric.infEDist_le_infEDist_add_edist

/-- `E_n` is continuous in `f`, being `1`-Lipschitz. -/
theorem continuous_approxError (n : ℕ) : Continuous (A.approxError · n) :=
  Metric.continuous_infEDist

/-- The errors tend to zero exactly for the elements of the closure of `⋃ n, A n`: the
decreasing errors tend to their infimum, the distance from `f` to `⋃ n, A n`. -/
theorem tendsto_approxError_zero_iff (f : X) :
    Tendsto (A.approxError f) atTop (𝓝 0) ↔ f ∈ closure (⋃ n, A n) := by
  have h := tendsto_atTop_iInf (approxError_anti (A := A) f)
  rw [Metric.mem_closure_iff_infEDist_zero, Metric.infEDist_iUnion]
  exact ⟨fun h0 => tendsto_nhds_unique h h0, fun h0 => h0 ▸ h⟩

/-- Since the errors decrease, they tend to zero as soon as the dyadic errors `E_{2^k}` do. -/
theorem tendsto_approxError_zero_of_pow {f : X}
    (h : Tendsto (fun k => A.approxError f (2 ^ k)) atTop (𝓝 0)) :
    Tendsto (A.approxError f) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero_iff_le_of_antitone (approxError_anti f)]
  intro ε hε
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.1 h ε hε
  exact ⟨2 ^ N, hN N le_rfl⟩

/-- **Functoriality of the error**: a bounded linear map that sends approximants to
approximants satisfies `E^B_n(T f) ≤ ‖T‖ E^A_n(f)`. -/
theorem approxError_map_le {B : ApproximationScheme Y} (T : X →L[ℝ] Y)
    (hT : ∀ n, ∀ a ∈ A n, T a ∈ B n) (f : X) (n : ℕ) :
    B.approxError (T f) n ≤ ‖T‖ₑ * A.approxError f n := by
  refine le_mul_approxError_of_forall_mem eNorm_ne_top fun a ha => ?_
  calc B.approxError (T f) n ≤ ‖T f - T a‖ₑ := approxError_le_of_mem (hT n a ha) _
    _ = ‖T (f - a)‖ₑ := by rw [map_sub]
    _ ≤ ‖T‖ₑ * ‖f - a‖ₑ := T.le_opENorm _

/-- **Bounds by a modulus pass from a dense set to all of `X`**: if `ω` is subadditive with
`ω(f) ≤ C₀ ‖f‖` and `E_n(g) ≤ C ω(g)` for all `g` in a dense set, then `E_n(f) ≤ C ω(f)` for every
`f`, since both sides move by at most a multiple of `‖f - g‖`
(`ApproximationScheme.approxError_le_approxError_add_enorm`). -/
theorem approxError_le_of_dense {D : Set X} (hD : Dense D)
    {ω : X → ℝ≥0∞} (hadd : ∀ f g, ω (f + g) ≤ ω f + ω g) {C0 : ℝ≥0∞} (hC0 : C0 ≠ ∞)
    (hle : ∀ f, ω f ≤ C0 * ‖f‖ₑ) {n : ℕ} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (h : ∀ g ∈ D, A.approxError g n ≤ C * ω g) (f : X) : A.approxError f n ≤ C * ω f := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  set K : ℝ≥0∞ := C * C0 + 1
  have hK : K ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hC hC0, ENNReal.one_ne_top⟩
  have hK0 : K ≠ 0 := by simp [K]
  obtain ⟨g, hgD, hfg⟩ := EMetric.mem_closure_iff.1 (hD f) (ε / K)
    (ENNReal.div_pos (by exact_mod_cast hε.ne') hK)
  have hdist : ‖f - g‖ₑ ≤ ε / K := by rw [← eDist_eq_eNorm_sub]; exact hfg.le
  have hmod : ω g ≤ ω f + C0 * ‖f - g‖ₑ := by
    have h1 := hadd f (g - f)
    rw [add_sub_cancel] at h1
    refine h1.trans (add_le_add le_rfl ((hle _).trans ?_))
    rw [← eNorm_neg, neg_sub]
  calc A.approxError f n
      ≤ A.approxError g n + ‖f - g‖ₑ := approxError_le_approxError_add_enorm n f g
    _ ≤ C * (ω f + C0 * ‖f - g‖ₑ) + ‖f - g‖ₑ := add_le_add ((h g hgD).trans (by gcongr)) le_rfl
    _ = C * ω f + K * ‖f - g‖ₑ := by simp only [K]; ring
    _ ≤ C * ω f + K * (ε / K) := by gcongr
    _ = C * ω f + ε := by rw [ENNReal.mul_div_cancel hK0 hK]

/-! ### The Lebesgue inequality -/

/-- **The Lebesgue inequality**: if an additive map `P` with `‖P x‖ ≤ C ‖x‖` fixes `a`, then
`‖f - P f‖ ≤ (1 + C) ‖f - a‖`, since `f - P f = (f - a) - P (f - a)`. -/
theorem norm_sub_apply_le_of_apply_eq {E F : Type*} [SeminormedAddCommGroup E] [FunLike F E E]
    [AddMonoidHomClass F E E] {P : F} {C : ℝ} (hP : ∀ x, ‖P x‖ ≤ C * ‖x‖) {a : E}
    (ha : P a = a) (f : E) : ‖f - P f‖ ≤ (1 + C) * ‖f - a‖ := by
  calc ‖f - P f‖ = ‖(f - a) - P (f - a)‖ := by rw [map_sub, ha]; abel_nf
    _ ≤ ‖f - a‖ + ‖P (f - a)‖ := norm_sub_le _ _
    _ ≤ ‖f - a‖ + C * ‖f - a‖ := by gcongr; exact hP _
    _ = (1 + C) * ‖f - a‖ := by ring

/-- **The Lebesgue inequality in extended norms**: if an additive map `P` with
`‖P x‖ ≤ C ‖x‖`, `C ∈ [0, ∞]`, fixes `a`, then `‖f - P f‖ ≤ (1 + C) ‖f - a‖`. -/
theorem enorm_sub_apply_le_of_apply_eq {E F : Type*} [SeminormedAddCommGroup E] [FunLike F E E]
    [AddMonoidHomClass F E E] {P : F} {C : ENNReal} (hP : ∀ x, ‖P x‖ₑ ≤ C * ‖x‖ₑ) {a : E}
    (ha : P a = a) (f : E) : ‖f - P f‖ₑ ≤ (1 + C) * ‖f - a‖ₑ := by
  calc ‖f - P f‖ₑ = ‖(f - a) - P (f - a)‖ₑ := by rw [map_sub, ha]; abel_nf
    _ ≤ ‖f - a‖ₑ + ‖P (f - a)‖ₑ := eNorm_sub_le
    _ ≤ ‖f - a‖ₑ + C * ‖f - a‖ₑ := by gcongr; exact hP _
    _ = (1 + C) * ‖f - a‖ₑ := by rw [add_mul, one_mul]

end ApproximationScheme
