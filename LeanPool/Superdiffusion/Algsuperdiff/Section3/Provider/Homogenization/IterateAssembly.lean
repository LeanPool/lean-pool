/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.FiniteCorridorIteration
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.FiniteRecurrence
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Homogenization.IterateInit

/-!
# IterateAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The finite-corridor iterate mean bound (`e.iter.post.new`)

The single public below is *exactly* the proposition that the proved terminal
theorem

`exists_isCommonEventTwoTermBigOWith_cutoffResponseJ_of_iterateMeanBound`
(`Provider/Homogenization/UnionCompletion.lean`)

takes as its one conditional A obligation `hIter`.  The statement below is a
byte-level transcription of that binder type, so the terminal theorem is
discharged by the bare application

```text
exists_isCommonEventTwoTermBigOWith_cutoffResponseJ_of_iterateMeanBound _
  (exists_iterateMeanBound_integral_cutoffResponseJ _)
```

with no glue at all.  This module is a Provider helper and makes no
source-node status claim by itself.

## What is assembled here, and from what

Three proved publics are consumed and nothing they prove is re-proved.

1. `exists_finiteRecurrence_integral_cutoffResponseJ`
   (`FiniteRecurrence.lean`) supplies the `A.4` recurrence constants
   `(Chom_R, A, C, j_0)` and, at every corridor depth `t` with `j_0 < t` and
   `Chom_R |log epsilon| <= t`, the display
   `F t <= A d_1 (d_1 + 3^{-t}) + C sum_{k=1}^t 3^{-k} (F(t-k) - F t)` for
   `F t := E[J(cu_{L+t}, sigmabar_L^{-1/2} e, sigmabar_L^{1/2} e; a_L)]` and
   `d_1 := 10^9 E^2 gamma`.  Its clause binder is carried at the *observation*
   scale `L + t`, so the proposition's own clause at `m - 1` supplies it
   exactly when `L + t <= m`.
2. `integral_cutoffResponseJ_nonneg_and_le_amplitude` (`IterateInit.lean`)
   supplies the engine's other two slots, `hFnonneg` and `hcrude` at `K_0 = 1`,
   **with no horizon**: `0 <= F t` and `F t <= d_1` for every `t : ℕ`.
3. `finiteCorridor_weightedDefect_iteration` (`FiniteCorridorIteration.lean`)
   is the weighted-mean engine.  The *existential* wrapper
   `exists_finiteCorridor_weightedDefect_decay` (`ibid.:475`) is **not** used:
   its `K` and `rho` are opaque witnesses, and the constant `Citer` produced
   below has to be built from them explicitly.  The fixed-constant public
   gives `finiteCorridorAmplitude A' (1/3) 0` and `rho =
   finiteCorridorDecayRate C` by name; the amplitude actually delivered by
   `exists_shift_engine` is `K = max (finiteCorridorAmplitude A' (1/3) 0) 1`,
   the `max` being what supplies the `1 <= K` that the final arithmetic needs
   (disclosed again at the `exists_shift_engine` entry below).  That is what
   makes `Citer` nameable before the model, the tolerance, the cutoff and the
   direction.

## The construction, and the two audit adjudications it implements

That is exactly what `truncated_shift_decay` below does: with `T:= (m -
L).toNat` it forms `G t:= if t <= T then F t else 0`, feeds `G` the *unbounded*
nonnegativity and crude bound of both branches, and establishes only the
recurrence by cases --- for `t <= T` it is the proved recurrence verbatim (the
clause binder at `L
+ t <= m` follows from the proposition's clause at `m - 1`), and for `t > T` it
degenerates to `0 <= (nonnegative)`.

The certified replacement, followed here, is a consumer-side shift with the
**sharp** geometric prefix `sum_{k > j} r^k <= (3/2) r^{j+1}` at `r = 1/3`,
absorbed into `A' := A + (3/2) r = A + C/2` (`geom_third_Icc_shift_le`,
`shifted_third_recurrence`), after which the engine is run at `j_0 = 0`, where
`finiteCorridorAmplitude A' (1/3) 0 = 2 (A' + 2)` is dimension-only and the
delivered amplitude is `K = max (finiteCorridorAmplitude A' (1/3) 0) 1`.  The
engine's own shift (its private `earlyPrefix_sum_le`, which pays a cardinality
factor `j_0`) is *not* bypassed: it is still invoked inside the engine
(`FiniteCorridorIteration.lean`), at `j_0 = 0`, where its cardinality factor
is `0`, so it is paid at zero cost.  The proved engine is not modified in any
way.

**The two separations.**  With `u := |log epsilon|`,

```text
t_0    := max (j_0 + 1) ceil(Chom_R u)        (the recurrence's own two binders)
j*     := ceil((log(4 * 10^9 * K) + u) * lam^{-1}),   lam := -log rho > 0
k_1    := t_0 + j*  .
```

`j*` is the least depth with `rho^{j*} (4 * 10^9 K) <= epsilon`; it is obtained
by taking logarithms (`Real.log_pow`, `Real.exp_log`) rather than through
`rpow`.  The budget `k_1 <= Citer u` is `shift_budget_le`, whose only analytic
input is `1 <= 2 u`, i.e. `|log epsilon| >= log 2 > 1/2`, which is where
`epsilon <= 1/2` is used.

**The constant.**

```text
Citer := max 1 (max Chom_R (max (4 K 10^18)
           (2 (j_0 + 3) + Chom_R + (2 log(4 * 10^9 K) + 1) lam^{-1}))) .
```

All four branches are dimension-only: they are built from `(Chom_R, A, C, j_0)`
and from `K, rho`, all selected before `M`, `E`, `epsilon`, `L`, `n`, `e`.  The
gate `gamma <= Citer^{-1} E^{-2} epsilon` implies the consumed gate
`gamma <= Chom_R^{-1} E^{-2} epsilon` because `Citer >= Chom_R` (monotone in the
right direction), and that one gate feeds *both* the recurrence and the
initialization, the latter at `Chom := Chom_R >= 10^9`, which is the floor the
amplitude bridge's gate route requires.

**The final arithmetic.**  At any `n` with `L + k_1 <= n <= m`, writing
`t := (n - L).toNat in [k_1, T]` and `j := t - t_0 >= j*`,

```text
F t <= K d_1 (d_1 + rho^j) <= K d_1 (d_1 + rho^{j*})
    <= (1/4) epsilon E^2 gamma + (1/4) epsilon E^2 gamma
     = 2^{-1} epsilon E^2 gamma ,
```

the first quarter from `K d_1^2 <= (1/4) epsilon E^2 gamma`, which needs only
`Citer >= 4 K 10^18`, and the second from the defining property of `j*`
(`final_absorption`).

## `d = 0`

The transcribed proposition quantifies over an arbitrary `d : ℕ`, exactly as
the terminal theorem and the frozen statement do, while both proved inputs
carry `[NeZero d]`.  The degenerate case is discharged from the standing model
itself: `M.shellPrefix.dimension : 2 <= d` is contradictory at `d = 0`, so the
whole inner `forall` is vacuous there and the witness `Citer := 1` serves.  For
`0 < d` the instance `NeZero d` is produced and the construction above runs.
No `[NeZero d]` binder is added to the statement, which is what makes the bare
application to the terminal theorem type-check.

## References

* ABK26, `e.iter.init`, `e.iter.post`, `k1` and `e.iter.post.new`,
  `p.homogenization.step`, the premises `epsilon in (0,1/2]` and
  `e.gamma.condition.homog`, `e.J.bound.by.indyhyp`.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book
open _root_.HCPolySupport.IndependentSums
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff

/-! ## Pure real arithmetic

Every step of the assembly that is not an instantiation of a proved public is
isolated here as a statement about abstract reals and abstract sequences: no
model, no measure, no observable occurs below until the final theorem. -/

/-- The geometric tail of the ratio-`1/3` series above a fixed index: `∑_{k =
j+1}^{N} 3^{-k} ≤ (1/2) 3^{-j}`. -/
private theorem geom_third_Icc_shift_le (j N : ℕ) :
    ∑ k ∈ Finset.Icc (j + 1) N, ((1 : ℝ) / 3) ^ k ≤
      (1 / 2 : ℝ) * ((1 : ℝ) / 3) ^ j := by
  have hIcc : Finset.Icc (j + 1) N = Finset.Ico (j + 1) (N + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have hterm : ∀ i ∈ Finset.range (N + 1 - (j + 1)),
      ((1 : ℝ) / 3) ^ (j + 1 + i) = ((1 : ℝ) / 3) ^ (j + 1) * ((1 : ℝ) / 3) ^ i :=
    fun i _ => pow_add _ _ _
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hgeom :=
    Algsuperdiff.Section3.Provider.Stream.sum_range_geom_third_le (N + 1 - (j + 1))
  have hpow : (0 : ℝ) ≤ ((1 : ℝ) / 3) ^ (j + 1) := by positivity
  calc ((1 : ℝ) / 3) ^ (j + 1) *
        ∑ i ∈ Finset.range (N + 1 - (j + 1)), ((1 : ℝ) / 3) ^ i
      ≤ ((1 : ℝ) / 3) ^ (j + 1) * (3 / 2) :=
        mul_le_mul_of_nonneg_left hgeom hpow
    _ = (1 / 2 : ℝ) * ((1 : ℝ) / 3) ^ j := by rw [pow_succ]; ring

/-- **The consumer-side shift.**  A finite weighted-defect recurrence available
only above a separation `t0`, together with the crude bound at `K₀ = 1` and
nonnegativity, becomes a recurrence for the shifted sequence `j ↦ G (t0 + j)`
available at every `j ≥ 1`, at the enlarged forcing coefficient `A + C/2` and
with the *same* defect coefficient `C`.

The lags that cross the shift are paid for by `geom_third_Icc_shift_le`, so the
enlargement `C/2 = (3/2)₀ r` at `K₀ = 1`, `r = 1/3` does not see `t0`.  That is
the whole point: the engine can then be run at `j₀ = 0`, where its amplitude
`finiteCorridorAmplitude` is independent of the shift. -/
private theorem shifted_third_recurrence {G : ℕ → ℝ} {A C delta : ℝ} (t0 : ℕ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hdelta : 0 ≤ delta)
    (hGnn : ∀ t : ℕ, 0 ≤ G t) (hGcr : ∀ t : ℕ, G t ≤ delta)
    (hGrec : ∀ t : ℕ, t0 < t →
      G t ≤ A * delta * (delta + (1 / 3 : ℝ) ^ t) +
        C * ∑ k ∈ Finset.Icc 1 t, (1 / 3 : ℝ) ^ k * (G (t - k) - G t)) :
    ∀ j : ℕ, 0 < j →
      G (t0 + j) ≤ (A + C * (1 / 2)) * delta * (delta + (1 / 3 : ℝ) ^ j) +
        C * ∑ k ∈ Finset.Icc 1 j,
          (1 / 3 : ℝ) ^ k * (G (t0 + (j - k)) - G (t0 + j)) := by
  intro j hj
  have hraw := hGrec (t0 + j) (by omega)
  have hsplit : Finset.Icc 1 (t0 + j) =
      Finset.Icc 1 j ∪ Finset.Icc (j + 1) (t0 + j) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 j) (Finset.Icc (j + 1) (t0 + j)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    have h1 := (Finset.mem_Icc.mp hk1).2
    have h2 := (Finset.mem_Icc.mp hk2).1
    omega
  rw [hsplit, Finset.sum_union hdisj] at hraw
  have hinternal :
      ∑ k ∈ Finset.Icc 1 j, (1 / 3 : ℝ) ^ k * (G (t0 + j - k) - G (t0 + j)) =
        ∑ k ∈ Finset.Icc 1 j,
          (1 / 3 : ℝ) ^ k * (G (t0 + (j - k)) - G (t0 + j)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkj : k ≤ j := (Finset.mem_Icc.mp hk).2
    have hidx : t0 + j - k = t0 + (j - k) := by omega
    rw [hidx]
  rw [hinternal] at hraw
  have hprefix :
      ∑ k ∈ Finset.Icc (j + 1) (t0 + j),
          (1 / 3 : ℝ) ^ k * (G (t0 + j - k) - G (t0 + j)) ≤
        delta * ((1 / 2 : ℝ) * ((1 : ℝ) / 3) ^ j) := by
    have hterm : ∀ k ∈ Finset.Icc (j + 1) (t0 + j),
        (1 / 3 : ℝ) ^ k * (G (t0 + j - k) - G (t0 + j)) ≤
          delta * ((1 : ℝ) / 3) ^ k := by
      intro k _
      have hdiff : G (t0 + j - k) - G (t0 + j) ≤ delta := by
        have h1 := hGcr (t0 + j - k)
        have h2 := hGnn (t0 + j)
        linarith
      calc (1 / 3 : ℝ) ^ k * (G (t0 + j - k) - G (t0 + j))
          ≤ (1 / 3 : ℝ) ^ k * delta :=
            mul_le_mul_of_nonneg_left hdiff (by positivity)
        _ = delta * ((1 : ℝ) / 3) ^ k := by ring
    calc ∑ k ∈ Finset.Icc (j + 1) (t0 + j),
          (1 / 3 : ℝ) ^ k * (G (t0 + j - k) - G (t0 + j))
        ≤ ∑ k ∈ Finset.Icc (j + 1) (t0 + j), delta * ((1 : ℝ) / 3) ^ k :=
          Finset.sum_le_sum hterm
      _ = delta * ∑ k ∈ Finset.Icc (j + 1) (t0 + j), ((1 : ℝ) / 3) ^ k := by
          rw [Finset.mul_sum]
      _ ≤ delta * ((1 / 2 : ℝ) * ((1 : ℝ) / 3) ^ j) :=
          mul_le_mul_of_nonneg_left (geom_third_Icc_shift_le j (t0 + j)) hdelta
  have hCpre := mul_le_mul_of_nonneg_left hprefix hC
  have hpow : (1 / 3 : ℝ) ^ (t0 + j) ≤ (1 / 3 : ℝ) ^ j :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hforce : A * delta * (delta + (1 / 3 : ℝ) ^ (t0 + j)) ≤
      A * delta * (delta + (1 / 3 : ℝ) ^ j) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hA hdelta)
  have hsq : (0 : ℝ) ≤ C * (1 / 2) * delta * delta :=
    mul_nonneg (mul_nonneg (mul_nonneg hC (by norm_num)) hdelta) hdelta
  linarith

/-- **Zero-truncation plus shift, feeding the proved engine at `j₀ = 0`.**

Truncating `F` to `G t := if t ≤ T then F t else 0` discharges exactly that
one slot: above `T` the recurrence degenerates to `0 ≤ (nonnegative)`, and the
other two slots are unaffected because both branches of the truncation satisfy
them.

The conclusion is stated at the engine's own named constants, so the amplitude
and the rate are available to the caller before any model datum is chosen. -/
private theorem truncated_shift_decay {F : ℕ → ℝ} {A C delta : ℝ} {T t0 : ℕ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hdelta : 0 ≤ delta)
    (hFnn : ∀ t : ℕ, 0 ≤ F t) (hFcr : ∀ t : ℕ, F t ≤ delta)
    (hFrec : ∀ t : ℕ, t0 < t → t ≤ T →
      F t ≤ A * delta * (delta + (1 / 3 : ℝ) ^ t) +
        C * ∑ k ∈ Finset.Icc 1 t, (1 / 3 : ℝ) ^ k * (F (t - k) - F t)) :
    ∀ j : ℕ, t0 + j ≤ T →
      F (t0 + j) ≤
        finiteCorridorAmplitude (A + C * (1 / 2)) C 1 (1 / 3) 0 * delta *
          (delta + finiteCorridorDecayRate C ^ j) := by
  classical
  set G : ℕ → ℝ := fun s => if s ≤ T then F s else 0 with hGdef
  have hGeq : ∀ s : ℕ, s ≤ T → G s = F s := by
    intro s hs
    simp only [hGdef, ite_eq_left hs]
  have hGnn : ∀ s : ℕ, 0 ≤ G s := by
    intro s
    simp only [hGdef]
    split
    · exact hFnn s
    · exact le_rfl
  have hGcr : ∀ s : ℕ, G s ≤ delta := by
    intro s
    simp only [hGdef]
    split
    · exact hFcr s
    · exact hdelta
  have hGrec : ∀ t : ℕ, t0 < t →
      G t ≤ A * delta * (delta + (1 / 3 : ℝ) ^ t) +
        C * ∑ k ∈ Finset.Icc 1 t, (1 / 3 : ℝ) ^ k * (G (t - k) - G t) := by
    intro t ht
    by_cases hT : t ≤ T
    · have hsum : ∑ k ∈ Finset.Icc 1 t,
          (1 / 3 : ℝ) ^ k * (G (t - k) - G t) =
            ∑ k ∈ Finset.Icc 1 t, (1 / 3 : ℝ) ^ k * (F (t - k) - F t) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hGeq (t - k) (by omega), hGeq t hT]
      rw [hsum, hGeq t hT]
      exact hFrec t ht hT
    · have hGt : G t = 0 := by
        simp only [hGdef, ite_eq_right hT]
      rw [hGt]
      have h2 : (0 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 t,
          (1 / 3 : ℝ) ^ k * (G (t - k) - 0) :=
        Finset.sum_nonneg fun k _ =>
          mul_nonneg (by positivity) (by simpa using hGnn (t - k))
      have h1 : (0 : ℝ) ≤ A * delta * (delta + (1 / 3 : ℝ) ^ t) :=
        mul_nonneg (mul_nonneg hA hdelta) (by positivity)
      linarith [mul_nonneg hC h2]
  have hcore := finiteCorridor_weightedDefect_iteration
    (F := fun s => G (t0 + s)) (A := A + C * (1 / 2)) (C := C) (K₀ := 1)
    (δ := delta) (r := (1 / 3 : ℝ)) (j₀ := 0)
    (by have hhalf := mul_nonneg hC (by norm_num : (0 : ℝ) ≤ 1 / 2); linarith)
    hC zero_le_one hdelta (by norm_num) le_rfl
    (fun s => hGnn (t0 + s))
    (fun s => by rw [one_mul]; exact hGcr (t0 + s))
    (fun s hs => shifted_third_recurrence t0 hA hC hdelta hGnn hGcr hGrec s hs)
  intro j hj
  have hres := hcore j
  simp only [zero_add] at hres
  rw [hGeq (t0 + j) hj] at hres
  exact hres

/-- **The engine, packaged at `j₀ = 0` behind the consumer-side shift.**  One
amplitude `K ≥ 1` and one rate `rho ∈ (0,1)`, built from the recurrence data
alone, such that a sequence with the unbounded crude bound and nonnegativity and
a recurrence on the corridor `[t0, T]` decays geometrically from depth `t0`.

`K ≥ 1` --- rather than `K ≥ 0` --- is arranged by a `max` so that the final
smallness arithmetic can divide by it. -/
private theorem exists_shift_engine (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∃ K rho : ℝ, 1 ≤ K ∧ 0 < rho ∧ rho < 1 ∧
      ∀ (F : ℕ → ℝ) (delta : ℝ) (T t0 : ℕ), 0 ≤ delta →
        (∀ t : ℕ, 0 ≤ F t) → (∀ t : ℕ, F t ≤ delta) →
        (∀ t : ℕ, t0 < t → t ≤ T →
          F t ≤ A * delta * (delta + (1 / 3 : ℝ) ^ t) +
            C * ∑ k ∈ Finset.Icc 1 t, (1 / 3 : ℝ) ^ k * (F (t - k) - F t)) →
        ∀ j : ℕ, t0 + j ≤ T → F (t0 + j) ≤ K * delta * (delta + rho ^ j) := by
  refine ⟨max (finiteCorridorAmplitude (A + C * (1 / 2)) C 1 (1 / 3) 0) 1,
    finiteCorridorDecayRate C, le_max_right _ _, finiteCorridorDecayRate_pos hC,
    finiteCorridorDecayRate_lt_one hC, ?_⟩
  intro F delta T t0 hdelta hFnn hFcr hFrec j hj
  refine le_trans (truncated_shift_decay hA hC hdelta hFnn hFcr hFrec j hj) ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hdelta)
    (add_nonneg hdelta (pow_nonneg (finiteCorridorDecayRate_pos hC).le j))

/-- **The final numeric absorption.**  At `Kp ≥ 1`, with `Esq * gamma` the
model's `E^2 gamma`, the amplitude `delta_1 = 10^9 E^2 gamma` and the geometric
remainder `P`, the smallness gate at `Citer ≥ 4 Kp 10^18` pays for the square
block and the defining property of the depth pays for the geometric block, each
with a quarter of `epsilon E^2 gamma` to spare. -/
private theorem final_absorption {Kp Esq gamma epsilon P Citer : ℝ}
    (hKp : 1 ≤ Kp) (hX : 0 ≤ Esq * gamma)
    (hCiterK : 4 * Kp * 10 ^ 18 ≤ Citer)
    (hgate : Esq * gamma ≤ Citer⁻¹ * epsilon)
    (hP : P * (4 * 10 ^ 9 * Kp) ≤ epsilon) :
    Kp * (10 ^ 9 * Esq * gamma) * (10 ^ 9 * Esq * gamma + P) ≤
      2⁻¹ * epsilon * Esq * gamma := by
  have hKp0 : (0 : ℝ) < Kp := by linarith
  have hlow : (0 : ℝ) < 4 * Kp * 10 ^ 18 := by positivity
  have hCpos : (0 : ℝ) < Citer := lt_of_lt_of_le hlow hCiterK
  have h1 : Citer * (Esq * gamma) ≤ epsilon := by
    have h := mul_le_mul_of_nonneg_left hgate hCpos.le
    rwa [mul_inv_cancel_left₀ (ne_of_gt hCpos)] at h
  have h2 : 4 * Kp * 10 ^ 18 * (Esq * gamma) ≤ epsilon :=
    le_trans (mul_le_mul_of_nonneg_right hCiterK hX) h1
  have h3 : Kp * 10 ^ 18 * (Esq * gamma) * (Esq * gamma) ≤
      epsilon / 4 * (Esq * gamma) :=
    mul_le_mul_of_nonneg_right (by linarith) hX
  have h5 : Kp * 10 ^ 9 * P * (Esq * gamma) ≤ epsilon / 4 * (Esq * gamma) :=
    mul_le_mul_of_nonneg_right (by linarith) hX
  calc Kp * (10 ^ 9 * Esq * gamma) * (10 ^ 9 * Esq * gamma + P)
      = Kp * 10 ^ 18 * (Esq * gamma) * (Esq * gamma) +
          Kp * 10 ^ 9 * P * (Esq * gamma) := by ring
    _ ≤ epsilon / 4 * (Esq * gamma) + epsilon / 4 * (Esq * gamma) := by
        linarith
    _ = 2⁻¹ * epsilon * Esq * gamma := by ring

/-- **The `k₁` budget**, in abstract form.  Two ceilings, one of `b u` and one of
`(Lb + u) W`, add up to a single multiple of `u`; the additive constants are
absorbed against `1 ≤ 2 u`, which is `|log epsilon| ≥ log 2` and the only place
`epsilon ≤ 1/2` is used. -/
private theorem shift_budget_le {a b Lb W u T0 Js : ℝ}
    (ha : 0 ≤ a) (hLb : 0 ≤ Lb) (hW : 0 ≤ W) (hu : 1 ≤ 2 * u)
    (hT0 : T0 ≤ a + 2 + b * u) (hJs : Js ≤ (Lb + u) * W + 1) :
    T0 + Js ≤ (2 * (a + 3) + b + (2 * Lb + 1) * W) * u := by
  have hQ : 0 ≤ a + 3 + Lb * W := by
    have hprod := mul_nonneg hLb hW
    linarith
  have hkey : 0 ≤ (a + 3 + Lb * W) * (2 * u - 1) := mul_nonneg hQ (by linarith)
  linarith

/-! ## The iterate mean bound -/

/-- One dimension-only constant `Citer ≥ 1` is selected before the model, the scale,
the tolerance, the cutoff and the direction.  Under the frozen regime binders
`15 c_star^{-1} ≤ E` and `gamma ≤ E^{-10}`, the preceding-error clause at every
scale `k ≤ m - 1`, the printed tolerance range `epsilon ∈ (0, 1/2]` and the
smallness gate `gamma ≤ Citer^{-1} E^{-2} epsilon`, a *single* separation `k₁` of
logarithmic size `k₁ ≤ Citer |log epsilon|` is fixed --- before any cutoff `L` and
any unit direction `e` --- such that

```text
E[J(cu_n, sigmabar_L^{-1/2} e, sigmabar_L^{1/2} e; a_L)] ≤ (1/2) epsilon E^2 gamma
```

at every cutoff `L ≤ m - 1`, every unit direction and every observation scale
`L + k₁ ≤ n ≤ m`.

This proposition is byte-identical to the `hIter` binder of the proved
`exists_isCommonEventTwoTermBigOWith_cutoffResponseJ_of_iterateMeanBound`
(`UnionCompletion.lean`, its), which it discharges by bare application.

This is a local Provider theorem and makes no source-node status claim. -/
theorem exists_iterateMeanBound_integral_cutoffResponseJ (d : ℕ) :
    ∃ Citer : ℝ, 1 ≤ Citer ∧
      ∀ (M : ABKModel d) (m : ℤ) (E : {E : ℝ // 1 ≤ E}),
        15 * (Disorder.cstar M)⁻¹ ≤ (E : ℝ) →
        M.gamma ≤ ((E : ℝ)⁻¹) ^ 10 →
        (∀ k : ℤ, k ≤ m - 1 →
          ∀ s : ℝ, ∀ hsWindow : s ∈ Set.Icc (8 * M.gamma) 1,
            Probability.IsTwoTermBigOWith
              (cutoffSampleLaw M).toMeasure
              (gammaSigma 2) (gammaSigma (1 / 2))
              (Observable.cutoffHomogenizationError M k
                ⟨s,
                  (mul_pos (by norm_num : (0 : ℝ) < 8)
                    M.shellPrefix.gamma_pos).trans_le hsWindow.1⟩)
              ((E : ℝ) * s⁻¹ * Real.sqrt M.gamma)
              ((s⁻¹) ^ 2 *
                Real.exp (-(((E : ℝ)⁻¹) ^ 3 * M.gamma⁻¹)))) →
        ∀ epsilon : ℝ, epsilon ∈ Set.Ioc 0 (1 / 2) →
          M.gamma ≤ Citer⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon →
          ∃ k1 : ℕ, (k1 : ℝ) ≤ Citer * |Real.log epsilon| ∧
            ∀ n L : ℤ, L ≤ m - 1 → L + k1 ≤ n → n ≤ m →
              ∀ e : Vec d, Ch02.vecNorm e = 1 →
                ∫ omega, Observable.cutoffResponseJ M n L e omega
                    ∂(cutoffSampleLaw M).toMeasure ≤
                  2⁻¹ * epsilon * (E : ℝ) ^ 2 * M.gamma := by
  classical
  -- the degenerate dimension: the standing model already excludes it
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · exact ⟨1, le_refl 1, fun M => absurd M.shellPrefix.dimension (by omega)⟩
  have : NeZero d := ⟨by omega⟩
  -- the `A.4` recurrence constants and the engine, both dimension-only
  obtain ⟨ChomR, A, C, j0R, hChom10, hChom64, hA, hC, hrecMain⟩ :=
    exists_finiteRecurrence_integral_cutoffResponseJ d
  obtain ⟨K, rho, hK1, hrho0, hrho1, hshift⟩ := exists_shift_engine A C hA hC
  obtain ⟨lam, hlamdef⟩ : ∃ x : ℝ, x = -Real.log rho := ⟨_, rfl⟩
  have hlam : 0 < lam := by
    have hlogneg : Real.log rho < 0 := Real.log_neg hrho0 hrho1
    rw [hlamdef]
    linarith
  have hKpos : (0 : ℝ) < K := by linarith
  obtain ⟨Lbig, hLbigdef⟩ : ∃ x : ℝ, x = Real.log (4 * 10 ^ 9 * K) := ⟨_, rfl⟩
  have hLbig0 : 0 ≤ Lbig := by
    rw [hLbigdef]
    exact Real.log_nonneg (by linarith)
  -- the four requirements on `Citer`, in one `max`
  obtain ⟨Citer, hCiterdef⟩ : ∃ x : ℝ, x = max 1 (max ChomR (max (4 * K * 10 ^ 18)
      (2 * ((j0R : ℝ) + 3) + ChomR + (2 * Lbig + 1) * lam⁻¹))) := ⟨_, rfl⟩
  have hCiter1 : (1 : ℝ) ≤ Citer := by rw [hCiterdef]; exact le_max_left _ _
  have hCiterChom : ChomR ≤ Citer := by
    rw [hCiterdef]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hCiterK : 4 * K * 10 ^ 18 ≤ Citer := by
    rw [hCiterdef]
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have hCiterB : 2 * ((j0R : ℝ) + 3) + ChomR + (2 * Lbig + 1) * lam⁻¹ ≤ Citer := by
    rw [hCiterdef]
    exact le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨Citer, hCiter1, ?_⟩
  intro M m E hEfloor hregime hLower epsilon heps hgate
  have hgammaPos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hE1 : (1 : ℝ) ≤ (E : ℝ) := E.property
  have hEpos : (0 : ℝ) < (E : ℝ) := lt_of_lt_of_le zero_lt_one hE1
  have hepsPos : (0 : ℝ) < epsilon := heps.1
  have hChomRpos : (0 : ℝ) < ChomR := by
    have h9 : (0 : ℝ) < 10 ^ 9 := by norm_num
    linarith
  have hCiterPos : (0 : ℝ) < Citer := by linarith
  -- the one gate feeds both proved inputs, at `Chom := ChomR ≥ 10 ^ 9`
  have hgateR : M.gamma ≤ ChomR⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon :=
    le_trans hgate
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (inv_anti₀ hChomRpos hCiterChom)
          (by positivity)) hepsPos.le)
  have habs0 : (0 : ℝ) ≤ |Real.log epsilon| := abs_nonneg _
  have hlogeps : Real.log epsilon = -|Real.log epsilon| := by
    have hle1 : epsilon ≤ 1 := le_trans heps.2 (by norm_num)
    have hnp : Real.log epsilon ≤ 0 := Real.log_nonpos hepsPos.le hle1
    rw [abs_of_nonpos hnp]
    ring
  have hone : (1 : ℝ) ≤ 2 * |Real.log epsilon| := by
    have hmono : Real.log epsilon ≤ Real.log (1 / 2 : ℝ) :=
      Real.log_le_log hepsPos heps.2
    have hval : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    rw [hval] at hmono
    have h2 := Real.log_two_gt_d9
    linarith
  -- the two separations, both selected before the cutoff and the direction
  obtain ⟨t0, ht0def⟩ : ∃ t : ℕ,
      t = max (j0R + 1) ⌈ChomR * |Real.log epsilon|⌉₊ := ⟨_, rfl⟩
  obtain ⟨jstar, hjstardef⟩ : ∃ t : ℕ,
      t = ⌈(Lbig + |Real.log epsilon|) * lam⁻¹⌉₊ := ⟨_, rfl⟩
  have hj0R : j0R < t0 := by rw [ht0def]; omega
  have hceilChom : ChomR * |Real.log epsilon| ≤ (t0 : ℝ) := by
    have h1 : ⌈ChomR * |Real.log epsilon|⌉₊ ≤ t0 := by rw [ht0def]; omega
    exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr h1)
  refine ⟨t0 + jstar, ?_, ?_⟩
  · -- the printed budget `k₁ ≤ Citer |log epsilon|`
    have hT0 : (t0 : ℝ) ≤ (j0R : ℝ) + 2 + ChomR * |Real.log epsilon| := by
      have h1 : t0 ≤ j0R + 1 + ⌈ChomR * |Real.log epsilon|⌉₊ := by
        rw [ht0def]; omega
      have h2 : ((⌈ChomR * |Real.log epsilon|⌉₊ : ℕ) : ℝ) ≤
          ChomR * |Real.log epsilon| + 1 :=
        (Nat.ceil_lt_add_one (mul_nonneg hChomRpos.le habs0)).le
      have h3 : ((t0 : ℕ) : ℝ) ≤
          ((j0R + 1 + ⌈ChomR * |Real.log epsilon|⌉₊ : ℕ) : ℝ) :=
        Nat.cast_le.mpr h1
      push_cast at h3
      linarith
    have hJs : (jstar : ℝ) ≤ (Lbig + |Real.log epsilon|) * lam⁻¹ + 1 := by
      rw [hjstardef]
      exact (Nat.ceil_lt_add_one
        (mul_nonneg (by linarith) (inv_nonneg.mpr hlam.le))).le
    have hbud := shift_budget_le (a := (j0R : ℝ)) (b := ChomR) (Lb := Lbig)
      (W := lam⁻¹) (u := |Real.log epsilon|) (T0 := (t0 : ℝ)) (Js := (jstar : ℝ))
      (Nat.cast_nonneg j0R) hLbig0 (inv_nonneg.mpr hlam.le) hone hT0 hJs
    have hmono := mul_le_mul_of_nonneg_right hCiterB habs0
    push_cast
    linarith
  · intro n L hLm1 hkn hnm e he
    -- the corridor depth and its horizon, as natural numbers
    obtain ⟨T, hTdef⟩ : ∃ T : ℕ, (T : ℤ) = m - L := ⟨(m - L).toNat, by omega⟩
    obtain ⟨t, htdef⟩ : ∃ t : ℕ, (t : ℤ) = n - L := ⟨(n - L).toNat, by omega⟩
    have hntL : L + (t : ℤ) = n := by omega
    have htT : t ≤ T := by omega
    have htk : t0 + jstar ≤ t := by omega
    have hLTm : L + (T : ℤ) = m := by omega
    rw [← hntL]
    -- the initialization: both engine slots, unbounded in the depth
    obtain ⟨hFnn, hFcr⟩ := integral_cutoffResponseJ_nonneg_and_le_amplitude M
      hChom10 hEfloor hregime hLower heps hgateR hLm1 he
    have hdelta0 : (0 : ℝ) ≤ 10 ^ 9 * (E : ℝ) ^ 2 * M.gamma :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hgammaPos.le
    -- the recurrence, on the corridor only: the clause descends from `m - 1`
    have hFrec : ∀ s : ℕ, t0 < s → s ≤ T →
        (∫ omega, Observable.cutoffResponseJ M (L + (s : ℤ)) L e omega
            ∂(cutoffSampleLaw M).toMeasure) ≤
          A * (10 ^ 9 * (E : ℝ) ^ 2 * M.gamma) *
              (10 ^ 9 * (E : ℝ) ^ 2 * M.gamma + (1 / 3 : ℝ) ^ s) +
            C * ∑ k ∈ Finset.Icc 1 s, (1 / 3 : ℝ) ^ k *
              ((∫ omega,
                  Observable.cutoffResponseJ M (L + ((s - k : ℕ) : ℤ)) L e omega
                    ∂(cutoffSampleLaw M).toMeasure) -
                ∫ omega, Observable.cutoffResponseJ M (L + (s : ℤ)) L e omega
                  ∂(cutoffSampleLaw M).toMeasure) := by
      intro s hs hsT
      refine hrecMain M E hEfloor hregime epsilon heps hgateR L e he s
        (by omega) ?_ ?_
      · have hcast : (t0 : ℝ) ≤ (s : ℝ) := Nat.cast_le.mpr (le_of_lt hs)
        linarith
      · intro k hk
        exact hLower k (by omega)
    have hdecay := hshift
      (fun s : ℕ => ∫ omega, Observable.cutoffResponseJ M (L + (s : ℤ)) L e omega
        ∂(cutoffSampleLaw M).toMeasure)
      (10 ^ 9 * (E : ℝ) ^ 2 * M.gamma) T t0 hdelta0 hFnn hFcr hFrec
      (t - t0) (by omega)
    have hidx : t0 + (t - t0) = t := by omega
    rw [hidx] at hdecay
    have hpow : rho ^ (t - t0) ≤ rho ^ jstar :=
      pow_le_pow_of_le_one hrho0.le hrho1.le (by omega)
    have hstep : (∫ omega, Observable.cutoffResponseJ M (L + (t : ℤ)) L e omega
          ∂(cutoffSampleLaw M).toMeasure) ≤
        K * (10 ^ 9 * (E : ℝ) ^ 2 * M.gamma) *
          (10 ^ 9 * (E : ℝ) ^ 2 * M.gamma + rho ^ jstar) := by
      refine le_trans hdecay ?_
      exact mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg (by linarith) hdelta0)
    refine le_trans hstep ?_
    have hXnn : (0 : ℝ) ≤ (E : ℝ) ^ 2 * M.gamma :=
      mul_nonneg (sq_nonneg _) hgammaPos.le
    have hEsq : (E : ℝ) ^ 2 * ((E : ℝ)⁻¹) ^ 2 = 1 := by
      field_simp
    have hgate' : (E : ℝ) ^ 2 * M.gamma ≤ Citer⁻¹ * epsilon := by
      have h := mul_le_mul_of_nonneg_left hgate (le_of_lt (pow_pos hEpos 2))
      calc (E : ℝ) ^ 2 * M.gamma
          ≤ (E : ℝ) ^ 2 * (Citer⁻¹ * ((E : ℝ)⁻¹) ^ 2 * epsilon) := h
        _ = Citer⁻¹ * epsilon * ((E : ℝ) ^ 2 * ((E : ℝ)⁻¹) ^ 2) := by ring
        _ = Citer⁻¹ * epsilon := by rw [hEsq, mul_one]
    have hprodpos : (0 : ℝ) < rho ^ jstar * (4 * 10 ^ 9 * K) :=
      mul_pos (pow_pos hrho0 _) (by linarith)
    have hjlam : Lbig + |Real.log epsilon| ≤ (jstar : ℝ) * lam := by
      have hceil : (Lbig + |Real.log epsilon|) * lam⁻¹ ≤ (jstar : ℝ) := by
        rw [hjstardef]; exact Nat.le_ceil _
      have h := mul_le_mul_of_nonneg_right hceil hlam.le
      rwa [inv_mul_cancel_right₀ (ne_of_gt hlam)] at h
    -- the defining property of the geometric depth `jstar`
    have hP : rho ^ jstar * (4 * 10 ^ 9 * K) ≤ epsilon := by
      have hlogle : Real.log (rho ^ jstar * (4 * 10 ^ 9 * K)) ≤
          Real.log epsilon := by
        rw [Real.log_mul (ne_of_gt (pow_pos hrho0 jstar))
            (ne_of_gt (by linarith : (0 : ℝ) < 4 * 10 ^ 9 * K)),
          Real.log_pow, ← hLbigdef, hlogeps]
        have hlogrho : Real.log rho = -lam := by rw [hlamdef]; ring
        rw [hlogrho]
        linarith
      have hexp := Real.exp_le_exp.mpr hlogle
      rwa [Real.exp_log hprodpos, Real.exp_log hepsPos] at hexp
    exact final_absorption hK1 hXnn hCiterK hgate' hP

end Algsuperdiff.Section3.Provider.Homogenization
