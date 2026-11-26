/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145SixFixedProducts
public import LeanPool.C145.C145PhysicalFrame

/-!
DRE6 Lemma 4.1: actual weighted physical necessity and exact whole-H2-fiber
affinity. Compile-free source proposal: no elaboration or kernel verdict.
All Pair sums include the ground output and the literal weights 1 / a(r)^2.
Power inputs range only over Fin n; v0 is not a ground mode. Real division
is totalized in the algebra. Nonzero overlaps enter physical necessity;
positive/injective nonground rates enter only the actual positive-data join.
Common rates, metric and ground entries are explicit calibration premises.
-/

@[expose] public section

noncomputable section
namespace C145.H2
open scoped BigOperators
variable {n : ℕ}

/-- Literal DRE6 (3.2), ordered d0,...,d5, with all n+1 outputs. -/
def fixedProducts (rates : Fin n → ℝ) (S : Tensor (n + 1)) :
    Fin 6 → Fin (n + 1) → ℝ :=
  ![fullPower rates S 0 0, fullPower rates S 0 1,
    fullPower rates S 0 2, fullPower rates S 1 1,
    fullPower rates S 0 3 + fullPower rates S 1 2,
    fullPower rates S 2 2 + (2 : ℝ) • fullPower rates S 0 4 +
      (2 : ℝ) • fullPower rates S 1 3]

/-- Literal eight rows A,...,H of (4.1), with the six covectors fixed. -/
def eightWith (a : Fin (n + 1) → ℝ) (rates : Fin n → ℝ)
    (d : Fin 6 → Fin (n + 1) → ℝ) (S : Tensor (n + 1))
    (f : Fin 8) (t : ℕ) : ℝ :=
  let B := C145PhysicalFrame.Pair a
  let P := fullPower rates S
  ![B (d 0) (P 1 t) - B (d 1) (P 0 t),
    B (d 1) (P 1 t) - B (d 3) (P 0 t),
    B (d 0) (P 2 t) - B (d 2) (P 0 t),
    B (d 1) (P 2 t) - B (d 2) (P 1 t),
    B (d 0) (P 3 t) + B (d 2) (P 1 t) - B (d 4) (P 0 t),
    2 * B (d 0) (P 4 t) + B (d 2) (P 2 t) +
      2 * B (d 1) (P 3 t) - B (d 5) (P 0 t),
    B (d 3) (P 2 t) + B (d 1) (P 3 t) - B (d 4) (P 1 t),
    B (d 4) (P 2 t) + B ((2 : ℝ) • d 3 - d 2) (P 3 t) +
      2 * B (d 1) (P 4 t) - B (d 5) (P 1 t)] f

/-- The eight indexed affine constraints specialized to the tensor's own fixed products. -/
def eight (a : Fin (n + 1) → ℝ) (rates : Fin n → ℝ)
    (S : Tensor (n + 1)) (f : Fin 8) (t : ℕ) : ℝ :=
  eightWith a rates (fixedProducts rates S) S f t

/-- The difference of the two pairings of the four modal powers. -/
def powerCurvature (a : Fin (n + 1) → ℝ) (rates : Fin n → ℝ)
    (S : Tensor (n + 1)) (i j k l : ℕ) : ℝ :=
  C145PhysicalFrame.Pair a (fullPower rates S i k) (fullPower rates S j l) -
    C145PhysicalFrame.Pair a (fullPower rates S i l) (fullPower rates S j k)

/-- The eight signed source curvature combinations, in the same A,...,H order. -/
def curvatureCombination (a : Fin (n + 1) → ℝ) (rates : Fin n → ℝ)
    (S : Tensor (n + 1)) (f : Fin 8) (t : ℕ) : ℝ :=
  let R := powerCurvature a rates S
  ![R 0 1 0 t, R 0 1 1 t, R 0 2 0 t,
    R 0 2 1 t - R 0 1 2 t, R 0 3 0 t + R 0 1 2 t,
    2 * R 0 4 0 t + R 0 2 2 t + 2 * R 0 3 1 t,
    R 1 2 1 t + R 0 3 1 t - R 0 1 3 t,
    -2 * R 0 1 4 t + R 0 2 3 t - R 0 3 2 t +
      2 * R 0 4 1 t + R 1 2 2 t + 2 * R 1 3 1 t] f

theorem pair_comm (a u v : Fin (n + 1) → ℝ) :
    C145PhysicalFrame.Pair a u v = C145PhysicalFrame.Pair a v u := by
  simp only [C145PhysicalFrame.Pair, mul_comm]

theorem pair_add_right (a u v w : Fin (n + 1) → ℝ) :
    C145PhysicalFrame.Pair a u (v + w) =
      C145PhysicalFrame.Pair a u v + C145PhysicalFrame.Pair a u w := by
  simp only [C145PhysicalFrame.Pair, Pi.add_apply, mul_add, add_div,
    Finset.sum_add_distrib]

theorem pair_sub_right (a u v w : Fin (n + 1) → ℝ) :
    C145PhysicalFrame.Pair a u (v - w) =
      C145PhysicalFrame.Pair a u v - C145PhysicalFrame.Pair a u w := by
  simp only [C145PhysicalFrame.Pair, Pi.sub_apply, mul_sub, sub_div,
    Finset.sum_sub_distrib]

theorem pair_smul_right (a u v : Fin (n + 1) → ℝ) (c : ℝ) :
    C145PhysicalFrame.Pair a u (c • v) = c * C145PhysicalFrame.Pair a u v := by
  simp only [C145PhysicalFrame.Pair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  ring

private theorem pair_add_left (a u v w : Fin (n + 1) → ℝ) :
    C145PhysicalFrame.Pair a (u + v) w =
      C145PhysicalFrame.Pair a u w + C145PhysicalFrame.Pair a v w := by
  rw [pair_comm a (u + v) w, pair_add_right, pair_comm a w u, pair_comm a w v]

private theorem pair_sub_left (a u v w : Fin (n + 1) → ℝ) :
    C145PhysicalFrame.Pair a (u - v) w =
      C145PhysicalFrame.Pair a u w - C145PhysicalFrame.Pair a v w := by
  rw [pair_comm a (u - v) w, pair_sub_right, pair_comm a w u, pair_comm a w v]

private theorem pair_smul_left (a u v : Fin (n + 1) → ℝ) (c : ℝ) :
    C145PhysicalFrame.Pair a (c • u) v = c * C145PhysicalFrame.Pair a u v := by
  rw [pair_comm a (c • u) v, pair_smul_right, pair_comm a v u]

theorem fullPower_add (rates : Fin n → ℝ) (U V : Tensor (n + 1))
    (p q : ℕ) (r : Fin (n + 1)) :
    fullPower rates (U + V) p q r =
      fullPower rates U p q r + fullPower rates V p q r := by
  simp only [fullPower, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem fullPower_smul (rates : Fin n → ℝ) (U : Tensor (n + 1)) (c : ℝ)
    (p q : ℕ) (r : Fin (n + 1)) :
    fullPower rates (c • U) p q r = c * fullPower rates U p q r := by
  simp only [fullPower, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private theorem fullPower_add_vector (rates : Fin n → ℝ) (U V : Tensor (n + 1))
    (p q : ℕ) : fullPower rates (U + V) p q =
      fullPower rates U p q + fullPower rates V p q := by
  funext r
  exact fullPower_add rates U V p q r

private theorem fullPower_sub_vector (rates : Fin n → ℝ) (U V : Tensor (n + 1))
    (p q : ℕ) : fullPower rates (V - U) p q =
      fullPower rates V p q - fullPower rates U p q := by
  funext r
  exact fullPower_sub rates U V p q r

private theorem fullPower_smul_vector (rates : Fin n → ℝ) (U : Tensor (n + 1))
    (c : ℝ) (p q : ℕ) : fullPower rates (c • U) p q = c • fullPower rates U p q := by
  funext r
  exact fullPower_smul rates U c p q r

/-- The literal six-vector table is exactly the accepted SameFullSix predicate. -/
theorem fixedProducts_eq_iff (rates : Fin n → ℝ) (U V : Tensor (n + 1)) :
    fixedProducts rates V = fixedProducts rates U ↔ SameFullSix rates U V := by
  constructor
  · intro h r
    have hd (f : Fin 6) := congrFun (congrFun h f) r
    exact ⟨by simpa [fixedProducts] using hd 0,
      by simpa [fixedProducts] using hd 1,
      by simpa [fixedProducts] using hd 2,
      by simpa [fixedProducts] using hd 3,
      by simpa [fixedProducts] using hd 4,
      by simpa [fixedProducts, smul_eq_mul] using hd 5⟩
  · intro h
    funext f r
    obtain ⟨h00, h01, h02, h11, h0312, h220413⟩ := h r
    fin_cases f
    · simpa [fixedProducts] using h00
    · simpa [fixedProducts] using h01
    · simpa [fixedProducts] using h02
    · simpa [fixedProducts] using h11
    · simpa [fixedProducts] using h0312
    · simpa [fixedProducts, smul_eq_mul] using h220413

theorem eightWith_add (a : Fin (n + 1) → ℝ) (rates : Fin n → ℝ)
    (d : Fin 6 → Fin (n + 1) → ℝ) (U V : Tensor (n + 1)) (f : Fin 8) (t : ℕ) :
    eightWith a rates d (U + V) f t =
      eightWith a rates d U f t + eightWith a rates d V f t := by
  fin_cases f <;>
    simp [eightWith, fullPower_add_vector, pair_add_right] <;> ring

theorem eightWith_sub (a : Fin (n + 1) → ℝ) (rates : Fin n → ℝ)
    (d : Fin 6 → Fin (n + 1) → ℝ) (U V : Tensor (n + 1)) (f : Fin 8) (t : ℕ) :
    eightWith a rates d (V - U) f t =
      eightWith a rates d V f t - eightWith a rates d U f t := by
  fin_cases f <;>
    simp [eightWith, fullPower_sub_vector, pair_sub_right] <;> ring

theorem eightWith_smul (a : Fin (n + 1) → ℝ) (rates : Fin n → ℝ)
    (d : Fin 6 → Fin (n + 1) → ℝ) (U : Tensor (n + 1)) (c : ℝ)
    (f : Fin 8) (t : ℕ) :
    eightWith a rates d (c • U) f t = c * eightWith a rates d U f t := by
  fin_cases f <;>
    simp [eightWith, fullPower_smul_vector, pair_smul_right] <;> ring

/-- Only the two input slots are used for the power swap. -/
theorem fullPower_swap (rates : Fin n → ℝ) (S : Tensor (n + 1))
    (hInput : ∀ x y r, S x y r = S y x r) (p q : ℕ) :
    fullPower rates S p q = fullPower rates S q p := by
  classical
  funext r
  unfold fullPower
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  rw [hInput i.succ j.succ r]
  ring

/-- Symmetry is derived from the actual cubic vertex sum for arbitrary Q,a. -/
theorem physical_input_symmetry
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ) (a : Fin (n + 1) → ℝ)
    (x y r : Fin (n + 1)) :
    C145PhysicalFrame.T Q a x y r = C145PhysicalFrame.T Q a y x r := by
  have hC : C145PhysicalFrame.C Q x y r = C145PhysicalFrame.C Q y x r := by
    unfold C145PhysicalFrame.C
    apply Finset.sum_congr rfl
    intro v hv
    ring
  unfold C145PhysicalFrame.T
  rw [hC]
  ring

/-- Expand the actual two power sums into four inputs and the full output sum.
No symmetry, nonzero weight, data, quotient or physicality hypothesis is used. -/
private theorem pair_fullPower_expansion (a : Fin (n + 1) → ℝ)
    (rates : Fin n → ℝ) (S : Tensor (n + 1)) (i j k l : ℕ) :
    C145PhysicalFrame.Pair a (fullPower rates S i k) (fullPower rates S j l) =
      ∑ α : Fin n, ∑ β : Fin n, ∑ γ : Fin n, ∑ δ : Fin n,
        (rates α ^ i * rates β ^ j * rates γ ^ k * rates δ ^ l) *
          ∑ r : Fin (n + 1), S α.succ γ.succ r * S β.succ δ.succ r / a r ^ 2 := by
  classical
  calc
    C145PhysicalFrame.Pair a (fullPower rates S i k) (fullPower rates S j l) =
        ∑ r : Fin (n + 1), ∑ α : Fin n, ∑ β : Fin n, ∑ γ : Fin n, ∑ δ : Fin n,
          (rates α ^ i * rates γ ^ k * S α.succ γ.succ r) *
            (rates β ^ j * rates δ ^ l * S β.succ δ.succ r) / a r ^ 2 := by
      simp only [C145PhysicalFrame.Pair, fullPower, Finset.sum_mul_sum, Finset.sum_div]
    _ = ∑ α : Fin n, ∑ β : Fin n, ∑ γ : Fin n, ∑ δ : Fin n,
        ∑ r : Fin (n + 1),
          (rates α ^ i * rates γ ^ k * S α.succ γ.succ r) *
            (rates β ^ j * rates δ ^ l * S β.succ δ.succ r) / a r ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro α hα
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro β hβ
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro γ hγ
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro α hα
      apply Finset.sum_congr rfl
      intro β hβ
      apply Finset.sum_congr rfl
      intro γ hγ
      apply Finset.sum_congr rfl
      intro δ hδ
      apply Finset.sum_congr rfl
      intro r hr
      ring

/-- Actual fivefold contraction to accepted modal Assoc, with its ground term. -/
theorem powerCurvature_eq_weighted_assoc (a : Fin (n + 1) → ℝ)
    (rates : Fin n → ℝ) (S : Tensor (n + 1)) (i j k l : ℕ) :
    powerCurvature a rates S i j k l =
      ∑ α : Fin n, ∑ β : Fin n, ∑ γ : Fin n, ∑ δ : Fin n,
        (rates α ^ i * rates β ^ j * rates γ ^ k * rates δ ^ l) *
          C145PhysicalFrame.Assoc a S α.succ β.succ γ.succ δ.succ := by
  classical
  have hCross :
      C145PhysicalFrame.Pair a (fullPower rates S i l) (fullPower rates S j k) =
        ∑ α : Fin n, ∑ β : Fin n, ∑ γ : Fin n, ∑ δ : Fin n,
          (rates α ^ i * rates β ^ j * rates γ ^ k * rates δ ^ l) *
            ∑ r : Fin (n + 1), S α.succ δ.succ r * S β.succ γ.succ r / a r ^ 2 := by
    rw [pair_fullPower_expansion]
    apply Finset.sum_congr rfl
    intro α hα
    apply Finset.sum_congr rfl
    intro β hβ
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro γ hγ
    apply Finset.sum_congr rfl
    intro δ hδ
    ring
  rw [powerCurvature, pair_fullPower_expansion, hCross]
  simp only [C145PhysicalFrame.Assoc, sub_div, Finset.sum_sub_distrib, mul_sub]

/-- All eight source combinations and signs. In particular D uses P21=P12;
H cancels P14 and P23=P32 and retains the coefficient 2*d3-d2. -/
theorem eight_eq_curvatureCombination (a : Fin (n + 1) → ℝ)
    (rates : Fin n → ℝ) (S : Tensor (n + 1))
    (hInput : ∀ x y r, S x y r = S y x r) (f : Fin 8) (t : ℕ) :
    eight a rates S f t = curvatureCombination a rates S f t := by
  have h10 := fullPower_swap rates S hInput 1 0
  have h20 := fullPower_swap rates S hInput 2 0
  have h30 := fullPower_swap rates S hInput 3 0
  have h40 := fullPower_swap rates S hInput 4 0
  have h21 := fullPower_swap rates S hInput 2 1
  have h31 := fullPower_swap rates S hInput 3 1
  have h41 := fullPower_swap rates S hInput 4 1
  have h32 := fullPower_swap rates S hInput 3 2
  fin_cases f <;>
    simp [eight, eightWith, fixedProducts, curvatureCombination, powerCurvature,
      h10, h20, h30, h40, h21, h31, h41, h32,
      pair_add_right, pair_sub_right, pair_smul_right, pair_comm] <;> ring

/-- Physical necessity comes from actual modal_associativity, never a desired
curvature premise. All n, all real rates and all power labels t are retained. -/
theorem physical_eight_necessary (rates : Fin n → ℝ)
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ) (a : Fin (n + 1) → ℝ)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q) (ha : ∀ r, a r ≠ 0)
    (f : Fin 8) (t : ℕ) : eight a rates (C145PhysicalFrame.T Q a) f t = 0 := by
  have hR (i j k l : ℕ) :
      powerCurvature a rates (C145PhysicalFrame.T Q a) i j k l = 0 := by
    rw [powerCurvature_eq_weighted_assoc]
    simp only [C145PhysicalFrame.modal_associativity Q a hQ ha,
      mul_zero, Finset.sum_const_zero]
  rw [eight_eq_curvatureCombination a rates (C145PhysicalFrame.T Q a)
    (physical_input_symmetry Q a)]
  fin_cases f <;> simp [curvatureCombination, hR]

/-- Restriction selects successor indices in every slot, never a ground input. -/
def residual (U : Tensor (n + 1)) : Tensor n :=
  fun i j k => U i.succ j.succ k.succ

/-- Prepend the common ground decay rate to the residual rates. -/
def fullRates (μ : ℝ) (rates : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cases μ rates

/-- Two tensors agree whenever any index is the ground mode. -/
def CommonGround (U0 U : Tensor (n + 1)) : Prop :=
  ∀ i j k, (i = 0 ∨ j = 0 ∨ k = 0) → U i j k = U0 i j k

/-- An explicitly calibrated full ordinary positive-H2 fiber; no physicality
or desired products, moments, curvature, affinity or rank is assumed. -/
def CommonGroundFiber (μ : ℝ) (rates : Fin n → ℝ) (U0 U : Tensor (n + 1)) : Prop :=
  FullSymTensor U ∧ CommonGround U0 U ∧ SamePositive (fullRates μ rates) U0 U

theorem commonGround_difference (U0 U : Tensor (n + 1)) (hG : CommonGround U0 U) :
    U - U0 = groundZero (residual U - residual U0) := by
  funext i j k
  refine Fin.cases ?_ (fun x => ?_) i
  · change U 0 j k - U0 0 j k = 0
    exact sub_eq_zero.mpr (hG 0 j k (Or.inl rfl))
  · refine Fin.cases ?_ (fun y => ?_) j
    · change U x.succ 0 k - U0 x.succ 0 k = 0
      exact sub_eq_zero.mpr (hG x.succ 0 k (Or.inr (Or.inl rfl)))
    · refine Fin.cases ?_ (fun z => ?_) k
      · change U x.succ y.succ 0 - U0 x.succ y.succ 0 = 0
        exact sub_eq_zero.mpr (hG x.succ y.succ 0 (Or.inr (Or.inr rfl)))
      · rfl

/-- Literal three full-index sums reduce only for the ground-zero difference.
No ground summand is deleted from a base tensor's physical pairing. -/
theorem H_groundZero (μ : ℝ) (rates : Fin n → ℝ) (E : Tensor n) (s t : ℝ) :
    H (fullRates μ rates) (groundZero E) s t = H rates E s t := by
  simp [H, Fin.sum_univ_succ, groundZero, fullRates]

theorem residual_fullSym (U : Tensor (n + 1)) (hU : FullSymTensor U) :
    FullSymTensor (residual U) := by
  intro e v
  exact hU e (Fin.succ ∘ v)

/-- Full positive ordinary data and explicit common ground imply the actual
residual data equality; neither calibration nor a quotient is supplied. -/
theorem samePositive_residual_of_commonGround (μ : ℝ) (rates : Fin n → ℝ)
    (U0 U : Tensor (n + 1)) (hG : CommonGround U0 U)
    (hH : SamePositive (fullRates μ rates) U0 U) :
    SamePositive rates (residual U0) (residual U) := by
  intro s t hs ht
  have hz : H (fullRates μ rates) (U - U0) s t = 0 := by
    rw [H_sub, ← hH s t hs ht, sub_self]
  rw [commonGround_difference U0 U hG, H_groundZero, H_sub] at hz
  exact (sub_eq_zero.mp hz).symm

/-- Reuse the accepted actual kernel/moments/six-products chain. -/
theorem commonGround_fiber_fixedProducts (μ : ℝ) (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (hPos : ∀ i, 0 < rates i)
    (U0 U : Tensor (n + 1)) (hU0 : FullSymTensor U0)
    (hFiber : CommonGroundFiber μ rates U0 U) :
    fixedProducts rates U = fixedProducts rates U0 := by
  apply (fixedProducts_eq_iff rates U0 U).mpr
  exact positive_H2_full_six_fixed rates hRates hPos (residual U0) (residual U)
    (residual_fullSym U0 hU0) (residual_fullSym U hFiber.1)
    (samePositive_residual_of_commonGround μ rates U0 U hFiber.2.1 hFiber.2.2)
    U0 U (commonGround_difference U0 U hFiber.2.1)

/-- Finite algebra helper: its fixed-product hypothesis is discharged from
actual ordinary H2 data in each source theorem below. -/
private theorem eight_affine_of_fixedProducts (a : Fin (n + 1) → ℝ)
    (rates : Fin n → ℝ) (U0 U : Tensor (n + 1))
    (hFixed : fixedProducts rates U = fixedProducts rates U0) (f : Fin 8) (t : ℕ) :
    eight a rates U f t = eight a rates U0 f t +
      eightWith a rates (fixedProducts rates U0) (U - U0) f t := by
  simp only [eight, hFixed]
  rw [eightWith_sub]
  ring

/-- Ordinary regular-data form: arbitrary injective real rates; explicit
full-ground difference; no positivity or physical-source assumption. -/
theorem ordinary_H2_eight_affine (rates : Fin n → ℝ) (hRates : Function.Injective rates)
    (a : Fin (n + 1) → ℝ) (E : Tensor n) (hSym : FullSymTensor E)
    (hData : NullRegular rates E) (U0 U : Tensor (n + 1))
    (hDiff : U - U0 = groundZero E) (f : Fin 8) (t : ℕ) :
    eight a rates U f t = eight a rates U0 f t +
      eightWith a rates (fixedProducts rates U0) (U - U0) f t := by
  apply eight_affine_of_fixedProducts a rates U0 U
  exact (fixedProducts_eq_iff rates U0 U).mpr
    (ordinary_H2_full_six_fixed rates hRates E hSym hData U0 U hDiff)

/-- Exact global difference identity at every point of the explicit full-data
fiber. It is not a tangent approximation, smallness claim, or uniqueness result. -/
theorem commonGround_fiber_eight_affine (μ : ℝ) (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (hPos : ∀ i, 0 < rates i)
    (a : Fin (n + 1) → ℝ) (U0 U : Tensor (n + 1)) (hU0 : FullSymTensor U0)
    (hFiber : CommonGroundFiber μ rates U0 U) (f : Fin 8) (t : ℕ) :
    eight a rates U f t = eight a rates U0 f t +
      eightWith a rates (fixedProducts rates U0) (U - U0) f t := by
  exact eight_affine_of_fixedProducts a rates U0 U
    (commonGround_fiber_fixedProducts μ rates hRates hPos U0 U hU0 hFiber) f t

private theorem H_add (rates : Fin n → ℝ) (U V : Tensor n) (s t : ℝ) :
    H rates (U + V) s t = H rates U s t + H rates V s t := by
  simp only [H, Pi.add_apply, add_div, Finset.sum_add_distrib]

private theorem H_smul (rates : Fin n → ℝ) (U : Tensor n) (c s t : ℝ) :
    H rates (c • U) s t = c * H rates U s t := by
  simp only [H, Pi.smul_apply, smul_eq_mul, mul_div_assoc, Finset.mul_sum]

/-- Every real barycentric combination remains in the actual common-ground
fiber, and all eight quadratic expressions obey the exact affine identity. -/
theorem commonGround_fiber_barycentric (μ : ℝ) (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (hPos : ∀ i, 0 < rates i)
    (a : Fin (n + 1) → ℝ) (U0 U1 U2 : Tensor (n + 1)) (hU0 : FullSymTensor U0)
    (h1 : CommonGroundFiber μ rates U0 U1) (h2 : CommonGroundFiber μ rates U0 U2)
    (θ : ℝ) (f : Fin 8) (t : ℕ) :
    CommonGroundFiber μ rates U0 ((1 - θ) • U1 + θ • U2) ∧
      eight a rates ((1 - θ) • U1 + θ • U2) f t =
        (1 - θ) * eight a rates U1 f t + θ * eight a rates U2 f t := by
  have hMix : CommonGroundFiber μ rates U0 ((1 - θ) • U1 + θ • U2) := by
    refine ⟨?_, ?_, ?_⟩
    · intro e v
      exact congrArg₂ (fun x y : ℝ => (1 - θ) * x + θ * y) (h1.1 e v) (h2.1 e v)
    · intro i j k hg
      change (1 - θ) * U1 i j k + θ * U2 i j k = U0 i j k
      rw [h1.2.1 i j k hg, h2.2.1 i j k hg]
      ring
    · intro s u hs hu
      rw [H_add, H_smul, H_smul, ← h1.2.2 s u hs hu, ← h2.2.2 s u hs hu]
      ring
  have hd1 := commonGround_fiber_fixedProducts μ rates hRates hPos U0 U1 hU0 h1
  have hd2 := commonGround_fiber_fixedProducts μ rates hRates hPos U0 U2 hU0 h2
  have hdMix := commonGround_fiber_fixedProducts μ rates hRates hPos U0
    ((1 - θ) • U1 + θ • U2) hU0 hMix
  refine ⟨hMix, ?_⟩
  simp only [eight, hdMix, hd1, hd2, eightWith_add, eightWith_smul]

/-- Actual physical members satisfy the fixed-d equations even when the
chosen common-data origin is nonphysical. This alone asserts no injectivity. -/
theorem physical_member_fiber_constraints (μ : ℝ) (rates : Fin n → ℝ)
    (hRates : Function.Injective rates) (hPos : ∀ i, 0 < rates i)
    (a : Fin (n + 1) → ℝ) (Q : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hQ : C145PhysicalFrame.ColumnOrthonormal Q) (ha : ∀ r, a r ≠ 0)
    (U0 : Tensor (n + 1)) (hU0 : FullSymTensor U0)
    (hFiber : CommonGroundFiber μ rates U0 (C145PhysicalFrame.T Q a))
    (f : Fin 8) (t : ℕ) :
    eightWith a rates (fixedProducts rates U0) (C145PhysicalFrame.T Q a) f t = 0 := by
  have hd := commonGround_fiber_fixedProducts μ rates hRates hPos U0
    (C145PhysicalFrame.T Q a) hU0 hFiber
  simpa only [eight, hd] using physical_eight_necessary rates Q a hQ ha f t

/-- Empty nonground inputs give zero in all eight rows, including the one
remaining ground output. No finite residual index is chosen. -/
theorem eight_n0 (a : Fin 1 → ℝ) (rates : Fin 0 → ℝ)
    (S : Tensor 1) (f : Fin 8) (t : ℕ) : eight a rates S f t = 0 := by
  fin_cases f <;> simp [eight, eightWith, fixedProducts, fullPower, C145PhysicalFrame.Pair]

end C145.H2

end
