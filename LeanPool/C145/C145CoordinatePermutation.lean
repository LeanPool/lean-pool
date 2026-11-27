/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified from the C145 v0.6 release for Lean Pool's pinned toolchain. -/

module

public import LeanPool.C145.C145SmallPhysicalTraceSeparation
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic.Ring

/-!
C145: actual finite-coordinate multiplication and one derived vertex permutation.

All sums retain every vertex/mode in Fin (n+1), including the ground and n=0.
Column orthonormality derives row completeness. Literal cubic equality derives
full pointwise multiplicativity; real coordinate idempotents and column norms
derive a bijection. No multiplicativity, unit, rank, injection or permutation
is supplied as a scientific premise. The calibrated H2 join is only n <= 4.
Raw temporal jets, unknown N, calibration, spectral representation and graph
positivity remain upstream of these finite sums.
-/

@[expose] public section

noncomputable section
namespace C145CoordinatePermutation
open scoped BigOperators

/-- The change of vertex coordinates obtained by multiplying the second frame by the first
transpose. -/
def transport {n : ℕ}
    (Q0 Q1 : Fin (n + 1) → Fin (n + 1) → ℝ) :
    Fin (n + 1) → Fin (n + 1) → ℝ :=
  fun w v => ∑ i, Q1 w i * Q0 v i

/-- Apply the modal transport matrix to a vertex vector. -/
def applyTransport {n : ℕ}
    (Q0 Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (f : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun w => ∑ v, transport Q0 Q1 w v * f v

/-- The vertex coordinate vector supported at one index with value one. -/
def coordinateVector {n : ℕ} (v : Fin (n + 1)) :
    Fin (n + 1) → ℝ :=
  fun u => if u = v then 1 else 0

/-- Reconstruct the generator from the frame and the negatives of its modal decay rates. -/
def spectralGenerator {n : ℕ}
    (lam : Fin (n + 1) → ℝ)
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ) :
    Fin (n + 1) → Fin (n + 1) → ℝ :=
  fun v u => -(∑ i, lam i * Q v i * Q u i)

/-- Reconstruct the signed port by weighting the modal columns with their overlaps. -/
def spectralPort {n : ℕ}
    (a : Fin (n + 1) → ℝ)
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun v => ∑ i, a i * Q v i

/-- Recover the Laplacian by removing the common decay from the negative generator. -/
def decayLaplacian {n : ℕ}
    (μ : ℝ) (lam : Fin (n + 1) → ℝ)
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ) :
    Fin (n + 1) → Fin (n + 1) → ℝ :=
  fun v u => -spectralGenerator lam Q v u -
    μ * (if v = u then 1 else 0)

theorem transport_eq_matrix_mul_transpose {n : ℕ}
    (Q0 Q1 : Fin (n + 1) → Fin (n + 1) → ℝ) :
    Matrix.of (transport Q0 Q1) =
      Matrix.of Q1 * (Matrix.of Q0).transpose := by
  ext w v
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, transport]

/-- A literal sum rearrangement; no frame hypothesis is needed. -/
private theorem applyTransport_mode_expansion {n : ℕ}
    (Q0 Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (f : Fin (n + 1) → ℝ) (w : Fin (n + 1)) :
    applyTransport Q0 Q1 f w =
      ∑ i, (∑ u, Q0 u i * f u) * Q1 w i := by
  classical
  calc
    applyTransport Q0 Q1 f w =
        ∑ v, ∑ i, Q0 v i * f v * Q1 w i := by
      simp only [applyTransport, transport, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ i, ∑ v, Q0 v i * f v * Q1 w i := Finset.sum_comm
    _ = ∑ i, (∑ u, Q0 u i * f u) * Q1 w i := by
      simp only [Finset.sum_mul]

theorem frame_reconstruction {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q)
    (f : Fin (n + 1) → ℝ) (v : Fin (n + 1)) :
    (∑ i, (∑ u, Q u i * f u) * Q v i) = f v := by
  classical
  have hRows := C145PhysicalFrame.columnOrthonormal_rowComplete Q hQ
  calc
    (∑ i, (∑ u, Q u i * f u) * Q v i) =
        ∑ u, f u * (∑ i, Q u i * Q v i) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ u, f u * (if u = v then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [hRows u v]
    _ = f v := by
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]

theorem transport_frame_column {n : ℕ}
    (Q0 Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hQ0 : C145PhysicalFrame.ColumnOrthonormal Q0)
    (w i : Fin (n + 1)) :
    (∑ v, transport Q0 Q1 w v * Q0 v i) = Q1 w i := by
  classical
  change applyTransport Q0 Q1 (fun v => Q0 v i) w = Q1 w i
  rw [applyTransport_mode_expansion]
  calc
    _ = ∑ j, (if j = i then 1 else 0) * Q1 w j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hQ0 j i]
    _ = Q1 w i := by
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]

theorem transport_transpose_frame_column {n : ℕ}
    (Q0 Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1)
    (v i : Fin (n + 1)) :
    (∑ w, transport Q0 Q1 w v * Q1 w i) = Q0 v i := by
  classical
  calc
    (∑ w, transport Q0 Q1 w v * Q1 w i) =
        ∑ j, Q0 v j * (∑ w, Q1 w j * Q1 w i) := by
      simp only [transport, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro w hw
      ring
    _ = ∑ j, Q0 v j * (if j = i then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hQ1 j i]
    _ = Q0 v i := by
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]

theorem transport_columnOrthonormal {n : ℕ}
    (Q0 Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hQ0 : C145PhysicalFrame.ColumnOrthonormal Q0)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1) :
    C145PhysicalFrame.ColumnOrthonormal (transport Q0 Q1) := by
  classical
  intro v u
  have hRows := C145PhysicalFrame.columnOrthonormal_rowComplete Q0 hQ0
  calc
    (∑ w, transport Q0 Q1 w v * transport Q0 Q1 w u) =
        ∑ w, (∑ i, Q1 w i * Q0 v i) * transport Q0 Q1 w u := rfl
    _ = ∑ i, Q0 v i * (∑ w, transport Q0 Q1 w u * Q1 w i) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro w hw
      ring
    _ = ∑ i, Q0 v i * Q0 u i := by
      simp_rw [transport_transpose_frame_column Q0 Q1 hQ1]
    _ = if v = u then 1 else 0 := hRows v u

theorem transport_frame_product {n : ℕ}
    (Q0 Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1)
    (hC : C145PhysicalFrame.C Q0 = C145PhysicalFrame.C Q1)
    (w i j : Fin (n + 1)) :
    (∑ v, transport Q0 Q1 w v * Q0 v i * Q0 v j) =
      Q1 w i * Q1 w j := by
  classical
  have hRows := C145PhysicalFrame.columnOrthonormal_rowComplete Q1 hQ1
  calc
    (∑ v, transport Q0 Q1 w v * Q0 v i * Q0 v j) =
        ∑ k, Q1 w k * C145PhysicalFrame.C Q0 i j k := by
      simp only [transport, C145PhysicalFrame.C, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ = ∑ k, Q1 w k * C145PhysicalFrame.C Q1 i j k := by rw [hC]
    _ = ∑ z, (Q1 z i * Q1 z j) * (∑ k, Q1 w k * Q1 z k) := by
      simp only [C145PhysicalFrame.C, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ z, (Q1 z i * Q1 z j) * (if w = z then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hRows w z]
    _ = Q1 w i * Q1 w j := by
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]

/-- Cubic equality determines products of all actual coordinate vectors. -/
theorem transport_multiplicative {n : ℕ}
    (Q0 Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hQ0 : C145PhysicalFrame.ColumnOrthonormal Q0)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1)
    (hC : C145PhysicalFrame.C Q0 = C145PhysicalFrame.C Q1)
    (f g : Fin (n + 1) → ℝ) (w : Fin (n + 1)) :
    applyTransport Q0 Q1 (fun v => f v * g v) w =
      applyTransport Q0 Q1 f w * applyTransport Q0 Q1 g w := by
  classical
  let α : Fin (n + 1) → ℝ := fun i => ∑ u, Q0 u i * f u
  let β : Fin (n + 1) → ℝ := fun j => ∑ u, Q0 u j * g u
  have hf (v : Fin (n + 1)) : (∑ i, α i * Q0 v i) = f v :=
    frame_reconstruction Q0 hQ0 f v
  have hg (v : Fin (n + 1)) : (∑ j, β j * Q0 v j) = g v :=
    frame_reconstruction Q0 hQ0 g v
  calc
    applyTransport Q0 Q1 (fun v => f v * g v) w =
        ∑ v, transport Q0 Q1 w v *
          ((∑ i, α i * Q0 v i) * (∑ j, β j * Q0 v j)) := by
      unfold applyTransport
      apply Finset.sum_congr rfl
      intro v hv
      rw [hf v, hg v]
    _ = ∑ v, ∑ i, ∑ j,
        (α i * β j) * (transport Q0 Q1 w v * Q0 v i * Q0 v j) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.sum_mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i, ∑ j, (α i * β j) *
        (∑ v, transport Q0 Q1 w v * Q0 v i * Q0 v j) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, (α i * β j) * (Q1 w i * Q1 w j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [transport_frame_product Q0 Q1 hQ1 hC w i j]
    _ = (∑ i, α i * Q1 w i) * (∑ j, β j * Q1 w j) := by
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = applyTransport Q0 Q1 f w * applyTransport Q0 Q1 g w := by
      rw [applyTransport_mode_expansion Q0 Q1 f w,
        applyTransport_mode_expansion Q0 Q1 g w]

theorem applyTransport_coordinateVector {n : ℕ}
    (Q0 Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (v w : Fin (n + 1)) :
    applyTransport Q0 Q1 (coordinateVector v) w = transport Q0 Q1 w v := by
  classical
  simp only [applyTransport, coordinateVector, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem transport_entry_idempotent {n : ℕ}
    (Q0 Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hQ0 : C145PhysicalFrame.ColumnOrthonormal Q0)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1)
    (hC : C145PhysicalFrame.C Q0 = C145PhysicalFrame.C Q1)
    (w v : Fin (n + 1)) :
    transport Q0 Q1 w v * transport Q0 Q1 w v = transport Q0 Q1 w v := by
  classical
  have he : (fun u => coordinateVector v u * coordinateVector v u) =
      coordinateVector v := by
    funext u
    by_cases hu : u = v <;> simp [coordinateVector, hu]
  have h := transport_multiplicative Q0 Q1 hQ0 hQ1 hC
    (coordinateVector v) (coordinateVector v) w
  simpa only [he, applyTransport_coordinateVector] using h.symm

theorem transport_entry_zero_or_one {n : ℕ}
    (Q0 Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hQ0 : C145PhysicalFrame.ColumnOrthonormal Q0)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1)
    (hC : C145PhysicalFrame.C Q0 = C145PhysicalFrame.C Q1)
    (w v : Fin (n + 1)) :
    transport Q0 Q1 w v = 0 ∨ transport Q0 Q1 w v = 1 := by
  have hzero : transport Q0 Q1 w v * (transport Q0 Q1 w v - 1) = 0 := by
    calc
      _ = transport Q0 Q1 w v * transport Q0 Q1 w v - transport Q0 Q1 w v := by ring
      _ = 0 := by rw [transport_entry_idempotent Q0 Q1 hQ0 hQ1 hC w v, sub_self]
  rcases mul_eq_zero.mp hzero with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem transport_column_singleton {n : ℕ}
    (Q0 Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hQ0 : C145PhysicalFrame.ColumnOrthonormal Q0)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1)
    (hC : C145PhysicalFrame.C Q0 = C145PhysicalFrame.C Q1)
    (v : Fin (n + 1)) :
    ∃! w : Fin (n + 1), transport Q0 Q1 w v = 1 := by
  classical
  let S : Finset (Fin (n + 1)) :=
    Finset.univ.filter (fun w => transport Q0 Q1 w v = 1)
  have hU := transport_columnOrthonormal Q0 Q1 hQ0 hQ1
  have hcount : (S.card : ℝ) = 1 := by
    calc
      (S.card : ℝ) = (∑ w, if transport Q0 Q1 w v = 1 then (1 : ℝ) else 0) := by
        exact (Finset.sum_boole (fun w : Fin (n + 1) =>
          transport Q0 Q1 w v = 1) Finset.univ).symm
      _ = ∑ w, transport Q0 Q1 w v * transport Q0 Q1 w v := by
        apply Finset.sum_congr rfl
        intro w hw
        rcases transport_entry_zero_or_one Q0 Q1 hQ0 hQ1 hC w v with h | h
        · simp [h]
        · simp [h]
      _ = 1 := by simpa only [ite_true] using hU v v
  have hcard : S.card = 1 := Nat.cast_eq_one.mp hcount
  have hUnique := Finset.card_eq_one_iff_existsUnique.mp hcard
  simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hUnique

/-- The vertex bijection and its orientation are derived from actual U columns. -/
theorem cubic_equality_vertex_permutation {n : ℕ}
    (Q0 Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hQ0 : C145PhysicalFrame.ColumnOrthonormal Q0)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1)
    (hC : C145PhysicalFrame.C Q0 = C145PhysicalFrame.C Q1) :
    ∃ π : Equiv.Perm (Fin (n + 1)),
      (∀ w v, transport Q0 Q1 w v = if w = π v then 1 else 0) ∧
      (∀ v i, Q1 (π v) i = Q0 v i) := by
  classical
  have hSingleton (v : Fin (n + 1)) := transport_column_singleton Q0 Q1 hQ0 hQ1 hC v
  have hExists (v : Fin (n + 1)) : ∃ w, transport Q0 Q1 w v = 1 := by
    obtain ⟨w, hw, _⟩ := hSingleton v
    exact ⟨w, hw⟩
  let p : Fin (n + 1) → Fin (n + 1) := fun v => Classical.choose (hExists v)
  have hp (v : Fin (n + 1)) : transport Q0 Q1 (p v) v = 1 :=
    Classical.choose_spec (hExists v)
  have hDelta (w v : Fin (n + 1)) :
      transport Q0 Q1 w v = if w = p v then 1 else 0 := by
    by_cases hw : w = p v
    · rw [ite_eq_left hw, hw]
      exact hp v
    · have hNotOne : transport Q0 Q1 w v ≠ 1 := by
        intro h
        obtain ⟨z, hz, hUnique⟩ := hSingleton v
        exact hw ((hUnique w h).trans (hUnique (p v) (hp v)).symm)
      have hZero := (transport_entry_zero_or_one Q0 Q1 hQ0 hQ1 hC w v).resolve_right hNotOne
      simpa only [ite_eq_right hw] using hZero
  have hU := transport_columnOrthonormal Q0 Q1 hQ0 hQ1
  have hInjective : Function.Injective p := by
    intro v u hpu
    by_cases hvu : v = u
    · exact hvu
    · have hColumns (w : Fin (n + 1)) :
          transport Q0 Q1 w v = transport Q0 Q1 w u := by
        rw [hDelta w v, hDelta w u, hpu]
      have hNorm : (∑ w, transport Q0 Q1 w v * transport Q0 Q1 w u) = 1 := by
        calc
          _ = ∑ w, transport Q0 Q1 w v * transport Q0 Q1 w v := by
            apply Finset.sum_congr rfl
            intro w hw
            rw [← hColumns w]
          _ = 1 := by simpa only [ite_true] using hU v v
      have hOrth : (∑ w, transport Q0 Q1 w v * transport Q0 Q1 w u) = 0 := by
        simpa only [ite_eq_right hvu] using hU v u
      exact False.elim ((zero_ne_one : (0 : ℝ) ≠ 1) (hOrth.symm.trans hNorm))
  let π : Equiv.Perm (Fin (n + 1)) :=
    Equiv.ofBijective p ⟨hInjective, Finite.surjective_of_injective hInjective⟩
  have hPerm (w v : Fin (n + 1)) :
      transport Q0 Q1 w v = if w = π v then 1 else 0 := by
    change transport Q0 Q1 w v = if w = p v then 1 else 0
    exact hDelta w v
  refine ⟨π, hPerm, ?_⟩
  intro v i
  calc
    Q1 (π v) i = (∑ w, transport Q0 Q1 w v * Q1 w i) := by
      simp only [hPerm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
    _ = Q0 v i := transport_transpose_frame_column Q0 Q1 hQ1 v i

/-- One and the same derived vertex permutation transports all literal formulas. -/
theorem cubic_equality_spectral_transport {n : ℕ}
    (Q0 Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hQ0 : C145PhysicalFrame.ColumnOrthonormal Q0)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1)
    (hC : C145PhysicalFrame.C Q0 = C145PhysicalFrame.C Q1)
    (lam a : Fin (n + 1) → ℝ) (μ : ℝ) :
    ∃ π : Equiv.Perm (Fin (n + 1)),
      (∀ w v, transport Q0 Q1 w v = if w = π v then 1 else 0) ∧
      (∀ v i, Q1 (π v) i = Q0 v i) ∧
      (∀ v u, spectralGenerator lam Q1 (π v) (π u) =
        spectralGenerator lam Q0 v u) ∧
      (∀ v, spectralPort a Q1 (π v) = spectralPort a Q0 v) ∧
      (∀ v u, decayLaplacian μ lam Q1 (π v) (π u) =
        decayLaplacian μ lam Q0 v u) := by
  classical
  obtain ⟨π, hPerm, hRows⟩ := cubic_equality_vertex_permutation Q0 Q1 hQ0 hQ1 hC
  have hGenerator (v u : Fin (n + 1)) :
      spectralGenerator lam Q1 (π v) (π u) = spectralGenerator lam Q0 v u := by
    simp only [spectralGenerator, hRows]
  refine ⟨π, hPerm, hRows, hGenerator, ?_, ?_⟩
  · intro v
    simp only [spectralPort, hRows]
  · intro v u
    simp only [decayLaplacian, hGenerator, π.injective.eq_iff]

/-- Accepted calibrated ordinary H2 separation through total size N=n+1 <= 5. -/
theorem calibrated_small_H2_vertex_identification {n : ℕ}
    (μ : ℝ) (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (hPos : ∀ i, 0 < rates i)
    (Q0 Q1 : Fin (n + 1) → Fin (n + 1) → ℝ)
    (a : Fin (n + 1) → ℝ) (c : ℝ)
    (hQ0 : C145PhysicalFrame.ColumnOrthonormal Q0)
    (hQ1 : C145PhysicalFrame.ColumnOrthonormal Q1)
    (ha : ∀ r, a r ≠ 0)
    (hG0 : ∀ v, Q0 v 0 = c) (hG1 : ∀ v, Q1 v 0 = c)
    (hn : n ≤ 4)
    (hH : C145.H2.SamePositive (C145.H2.fullRates μ rates)
      (C145PhysicalFrame.T Q0 a) (C145PhysicalFrame.T Q1 a)) :
    ∃ π : Equiv.Perm (Fin (n + 1)),
      (∀ w v, transport Q0 Q1 w v = if w = π v then 1 else 0) ∧
      (∀ v i, Q1 (π v) i = Q0 v i) ∧
      (∀ v u, spectralGenerator (C145.H2.fullRates μ rates) Q1 (π v) (π u) =
        spectralGenerator (C145.H2.fullRates μ rates) Q0 v u) ∧
      (∀ v, spectralPort a Q1 (π v) = spectralPort a Q0 v) ∧
      (∀ v u, decayLaplacian μ (C145.H2.fullRates μ rates) Q1 (π v) (π u) =
        decayLaplacian μ (C145.H2.fullRates μ rates) Q0 v u) := by
  have hC := C145.H2.physical_small_H2_multiplication_equality μ rates hRates hPos
    Q0 Q1 a c hQ0 hQ1 ha hG0 hG1 hn hH
  exact cubic_equality_spectral_transport Q0 Q1 hQ0 hQ1 hC
    (C145.H2.fullRates μ rates) a μ


end C145CoordinatePermutation
end

end
