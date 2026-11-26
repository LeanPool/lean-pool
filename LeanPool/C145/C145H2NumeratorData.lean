/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145ThreePlaneFactor
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Polynomial
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Order

/-!
C145 ordinary residual H2: actual finite numerator, regular positive data,
and the n <= 3 injection join. Compile-free source proposal only.

Coordinates are z=X 0, x=X 1, y=X 2, exactly as in C145ThreePlaneFactor.
E i j k means the x-input, y-input, z-output coefficient. All three slots
are symmetric only where FullSymTensor is explicitly assumed.

Products remain symbolic and unexpanded. Distinctness is used only for
individual gaps; positivity is used only in the named physical corollaries.
No grid inverse, all-n residue converse, moments, or physical trace is assumed.
-/

@[expose] public section

noncomputable section

namespace C145.H2

open MvPolynomial C145.ThreePlane
open scoped BigOperators

/-- A real cubic tensor on a finite modal index set. -/
abbrev Tensor (n : ℕ) := Fin n → Fin n → Fin n → ℝ

/-- D(u) = product_h (u + lambda_h), including D=1 when n=0. -/
def D {n : ℕ} (rates : Fin n → ℝ) : Polynomial ℝ :=
  ∏ h, (Polynomial.X + Polynomial.C (rates h))

/-- The literal erased product, not a quotient in a rational-function field. -/
def Li {n : ℕ} (rates : Fin n → ℝ) (i : Fin n) : Polynomial ℝ :=
  ∏ h ∈ (Finset.univ.erase i), (Polynomial.X + Polynomial.C (rates h))

/-- Oriented gap product D'(-lambda_i); signs are lambda_h-lambda_i. -/
def di {n : ℕ} (rates : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∏ h ∈ (Finset.univ.erase i), (rates h - rates i)

/-- Place the literal Li product in one of the three coordinates. -/
def L {n : ℕ} (rates : Fin n → ℝ) (i : Fin n) (r : Fin 3) : P3 :=
  ∏ h ∈ (Finset.univ.erase i), (X r + C (rates h))

/-- The actual common-denominator numerator, with the source slot order. -/
def numerator {n : ℕ} (rates : Fin n → ℝ) (E : Tensor n) : P3 :=
  ∑ i, ∑ j, ∑ k, C (E i j k) * L rates i 1 * L rates j 2 * L rates k 0

/-- Support formulation retains the exact n=0 meaning. -/
def Box (n : ℕ) (F : P3) : Prop :=
  ∀ m ∈ F.support, ∀ r : Fin 3, m r < n

/-- Read a tensor entry with the index order used in the permutation formulas. -/
def entry {n : ℕ} (E : Tensor n) (a : Fin 3 → Fin n) : ℝ :=
  E (a 1) (a 2) (a 0)

/-- Invariance under every permutation of all three slots, including output. -/
def FullSymTensor {n : ℕ} (E : Tensor n) : Prop :=
  ∀ (e : Equiv.Perm (Fin 3)) (a : Fin 3 → Fin n),
    entry E (a ∘ e) = entry E a

/-- Exactly the ordinary residual response from DRE4/DRE6. -/
def H {n : ℕ} (rates : Fin n → ℝ) (E : Tensor n) (s t : ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k,
    E i j k / ((s + rates i) * (t + rates j) * (s + t + rates k))

/-- Guard every factor; no equality of totalized values at poles is inferred. -/
def Regular {n : ℕ} (rates : Fin n → ℝ) (s t : ℝ) : Prop :=
  (∀ i, s + rates i ≠ 0) ∧ (∀ i, t + rates i ≠ 0) ∧
    (∀ i, s + t + rates i ≠ 0)

/-- The second transfer function vanishes at all positive regular inputs. -/
def NullRegular {n : ℕ} (rates : Fin n → ℝ) (E : Tensor n) : Prop :=
  ∀ s t, 0 < s → 0 < t → Regular rates s t → H rates E s t = 0

/-- The second transfer function vanishes at all positive inputs. -/
def NullPositive {n : ℕ} (rates : Fin n → ℝ) (E : Tensor n) : Prop :=
  ∀ s t, 0 < s → 0 < t → H rates E s t = 0

/-- The second transfer functions agree at all positive regular inputs. -/
def SameRegular {n : ℕ} (rates : Fin n → ℝ) (S T : Tensor n) : Prop :=
  ∀ s t, 0 < s → 0 < t → Regular rates s t → H rates S s t = H rates T s t

/-- The second transfer functions agree at all positive inputs. -/
def SamePositive {n : ℕ} (rates : Fin n → ℝ) (S T : Tensor n) : Prop :=
  ∀ s t, 0 < s → 0 < t → H rates S s t = H rates T s t

variable {n : ℕ}

/-- These are the actual literal products under polynomial substitution. -/
theorem L_eq_eval₂ (rates : Fin n → ℝ) (i : Fin n) (r : Fin 3) :
    L rates i r = Polynomial.eval₂ C (X r) (Li rates i) := by
  simp [L, Li, Polynomial.eval₂_finsetProd]

theorem eval_L (rates : Fin n → ℝ) (i : Fin n) (r : Fin 3)
    (w : Fin 3 → ℝ) :
    MvPolynomial.eval w (L rates i r) = (Li rates i).eval (w r) := by
  simp [L, Li, Polynomial.eval_prod]

theorem D_factor (rates : Fin n → ℝ) (i : Fin n) :
    D rates = (Polynomial.X + Polynomial.C (rates i)) * Li rates i := by
  exact (Finset.mul_prod_erase Finset.univ
    (fun h => Polynomial.X + Polynomial.C (rates h)) (Finset.mem_univ i)).symm

theorem eval_D_factor (rates : Fin n → ℝ) (i : Fin n) (u : ℝ) :
    (D rates).eval u = (u + rates i) * (Li rates i).eval u := by
  rw [D_factor rates i]
  simp

theorem eval_Li_node (rates : Fin n → ℝ) (i : Fin n) :
    (Li rates i).eval (-rates i) = di rates i := by
  simp [Li, di, Polynomial.eval_prod, sub_eq_add_neg, add_comm]

theorem di_ne_zero (rates : Fin n → ℝ) (hRates : Function.Injective rates) (i : Fin n) :
    di rates i ≠ 0 := by
  classical
  unfold di
  apply Finset.prod_ne_zero_iff.mpr
  intro h hh
  exact sub_ne_zero.mpr (fun he => (Finset.mem_erase.mp hh).1 (hRates he))

/-- Binds the source derivative notation to the same oriented erased product. -/
theorem eval_derivative_D_node (rates : Fin n → ℝ) (i : Fin n) :
    (D rates).derivative.eval (-rates i) = di rates i := by
  have hD : D rates = Lagrange.nodal Finset.univ (fun h => -rates h) := by
    simp [D, Lagrange.nodal]
  have hL : Li rates i = Lagrange.nodal (Finset.univ.erase i) (fun h => -rates h) := by
    simp [Li, Lagrange.nodal]
  rw [hD, Lagrange.eval_nodal_derivative_eval_node_eq
    (s := Finset.univ) (v := fun h : Fin n => -rates h) (i := i) (Finset.mem_univ i),
    ← hL, eval_Li_node]

/-- Off-diagonal vanishing uses a literal zero factor and needs no injection. -/
theorem eval_Li_other (rates : Fin n → ℝ) (i h : Fin n) (hhi : h ≠ i) :
    (Li rates i).eval (-rates h) = 0 := by
  classical
  simp only [Li, Polynomial.eval_prod, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hhi, Finset.mem_univ h⟩) (by ring)

theorem eval_Li_grid (rates : Fin n → ℝ) (i h : Fin n) :
    (Li rates i).eval (-rates h) = if i = h then di rates h else 0 := by
  by_cases hi : i = h
  · subst i
    simp [eval_Li_node]
  · simp [hi, eval_Li_other rates i h (Ne.symm hi)]

/-- Direct finite-sum evaluation; this is not an interpolation premise. -/
theorem numerator_eval_grid (rates : Fin n → ℝ) (E : Tensor n) (i j k : Fin n) :
    MvPolynomial.eval ![-rates k, -rates i, -rates j] (numerator rates E) =
      E i j k * di rates i * di rates j * di rates k := by
  classical
  simp [numerator, eval_L, eval_Li_grid]

/-- Numerator injection is obtained from its actual negative-node values. -/
theorem numerator_injective (rates : Fin n → ℝ) (hRates : Function.Injective rates) :
    Function.Injective (numerator rates) := by
  intro E F h
  funext i j k
  have hg := congrArg (MvPolynomial.eval ![-rates k, -rates i, -rates j]) h
  rw [numerator_eval_grid, numerator_eval_grid] at hg
  have h₁ := mul_right_cancel₀ (di_ne_zero rates hRates k) hg
  have h₂ := mul_right_cancel₀ (di_ne_zero rates hRates j) h₁
  exact mul_right_cancel₀ (di_ne_zero rates hRates i) h₂

theorem numerator_zero (rates : Fin n → ℝ) : numerator rates (0 : Tensor n) = 0 := by
  simp [numerator]

theorem numerator_eq_zero_iff (rates : Fin n → ℝ) (hRates : Function.Injective rates)
    (E : Tensor n) : numerator rates E = 0 ↔ E = 0 := by
  constructor
  · intro h
    apply numerator_injective rates hRates
    rw [h, numerator_zero]
  · rintro rfl
    exact numerator_zero rates

/-- Empty residual tensor and empty sums are retained, with no chosen grid node. -/
theorem numerator_n0 (rates : Fin 0 → ℝ) (E : Tensor 0) : numerator rates E = 0 := by
  simp [numerator]

theorem box_zero_iff (F : P3) : Box 0 F ↔ F = 0 := by
  classical
  constructor
  · intro hb
    ext m
    change F.coeff m = 0
    by_contra hm
    have hlt := hb m (MvPolynomial.mem_support_iff.mpr hm) 0
    omega
  · rintro rfl
    simp [Box]

theorem box_iff_degree_lt (hn : 0 < n) (F : P3) :
    Box n F ↔ ∀ r : Fin 3, degreeOf r F < n := by
  constructor
  · intro hb r
    exact (degreeOf_lt_iff hn).mpr (fun m hm => hb m hm r)
  · intro hd m hm r
    exact (monomial_le_degreeOf r hm).trans_lt (hd r)

private def tripleEquiv : (Fin n × (Fin n × Fin n)) ≃ (Fin 3 → Fin n) where
  toFun p := ![p.2.2, p.1, p.2.1]
  invFun a := (a 1, a 2, a 0)
  left_inv p := by rcases p with ⟨i, j, k⟩; rfl
  right_inv a := by funext r; fin_cases r <;> rfl

/-- A change of finite indexing only, exposing all-slot symmetry without
expanding the n-dependent Li products. The definition itself is the triple sum. -/
theorem numerator_as_sum (rates : Fin n → ℝ) (E : Tensor n) :
    numerator rates E = ∑ a : Fin 3 → Fin n,
      C (entry E a) * ∏ r : Fin 3, L rates (a r) r := by
  classical
  calc
    numerator rates E = ∑ p : Fin n × (Fin n × Fin n),
        C (E p.1 p.2.1 p.2.2) * L rates p.1 1 * L rates p.2.1 2 * L rates p.2.2 0 := by
      simp only [numerator, Fintype.sum_prod_type]
    _ = _ := Fintype.sum_equiv tripleEquiv _ _ (by
      intro p
      simp [tripleEquiv, entry, Fin.prod_univ_succ]; ring)

private theorem degree_L_le (rates : Fin n → ℝ) (i : Fin n) (r c : Fin 3) :
    degreeOf c (L rates i r) ≤ if c = r then n - 1 else 0 := by
  classical
  calc
    degreeOf c (L rates i r) ≤ ∑ h ∈ Finset.univ.erase i,
        degreeOf c (X r + C (rates h) : P3) := degreeOf_prod_le c _ _
    _ ≤ ∑ _h ∈ Finset.univ.erase i, (if c = r then 1 else 0) := by
      apply Finset.sum_le_sum
      intro h hh
      exact (degreeOf_add_le c _ _).trans (by simp [degreeOf_X])
    _ = if c = r then n - 1 else 0 := by
      by_cases h : c = r <;> simp [h, Finset.card_erase_of_mem]

private theorem degree_term_le (rates : Fin n → ℝ) (E : Tensor n)
    (a : Fin 3 → Fin n) (c : Fin 3) :
    degreeOf c (C (entry E a) * ∏ r : Fin 3, L rates (a r) r) ≤ n - 1 := by
  classical
  calc
    degreeOf c (C (entry E a) * ∏ r : Fin 3, L rates (a r) r) ≤
        0 + ∑ r : Fin 3, degreeOf c (L rates (a r) r) :=
      (degreeOf_mul_le c _ _).trans (by
        rw [degreeOf_C]
        exact Nat.add_le_add_left (degreeOf_prod_le c _ _) 0)
    _ ≤ 0 + ∑ r : Fin 3, (if c = r then n - 1 else 0) := by
      exact Nat.add_le_add_left (Finset.sum_le_sum (fun r _ => degree_L_le rates (a r) r c)) 0
    _ = n - 1 := by simp

/-- Support Box is derived from the literal numerator at every n, without
rate injection, tensor symmetry, or any caller-supplied degree bound. -/
theorem numerator_box (rates : Fin n → ℝ) (E : Tensor n) : Box n (numerator rates E) := by
  classical
  by_cases hn : n = 0
  · subst n
    exact (box_zero_iff _).mpr (numerator_n0 rates E)
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    apply (box_iff_degree_lt hnpos _).mpr
    intro c
    have hd : degreeOf c (numerator rates E) ≤ n - 1 := by
      rw [numerator_as_sum]
      exact (degreeOf_sum_le c _ _).trans (Finset.sup_le (fun a _ => degree_term_le rates E a c))
    omega

private theorem rename_L (rates : Fin n → ℝ) (i : Fin n)
    (e : Equiv.Perm (Fin 3)) (r : Fin 3) :
    rename e (L rates i r) = L rates i (e r) := by
  simp [L]

private def reindex (e : Equiv.Perm (Fin 3)) :
    (Fin 3 → Fin n) ≃ (Fin 3 → Fin n) where
  toFun a := a ∘ e.symm
  invFun a := a ∘ e
  left_inv a := by funext r; simp
  right_inv a := by funext r; simp

/-- Full tensor symmetry gives the accepted all-coordinate SymPoly interface. -/
theorem numerator_symmetric (rates : Fin n → ℝ) (E : Tensor n)
    (hE : FullSymTensor E) : SymPoly (numerator rates E) := by
  classical
  intro e
  let f : (Fin 3 → Fin n) → P3 := fun a =>
    C (entry E a) * ∏ r : Fin 3, L rates (a r) r
  have hf : numerator rates E = ∑ a : Fin 3 → Fin n, f a :=
    numerator_as_sum rates E
  have hterm (a : Fin 3 → Fin n) : rename e (f a) = f (reindex e a) := by
    have hc : entry E (reindex e a) = entry E a := hE e.symm a
    have hp : (∏ r : Fin 3, L rates (a r) (e r)) =
        ∏ r : Fin 3, L rates ((reindex e a) r) r := by
      calc
        (∏ r : Fin 3, L rates (a r) (e r)) =
            ∏ r : Fin 3, L rates ((reindex e a) (e r)) (e r) := by
          apply Finset.prod_congr rfl
          intro r hr
          change L rates (a r) (e r) = L rates (a (e.symm (e r))) (e r)
          rw [e.symm_apply_apply]
        _ = ∏ r : Fin 3, L rates ((reindex e a) r) r :=
          _root_.Equiv.prod_comp e (fun r => L rates ((reindex e a) r) r)
    change rename e (C (entry E a) * ∏ r : Fin 3, L rates (a r) r) =
      C (entry E (reindex e a)) * ∏ r : Fin 3, L rates ((reindex e a) r) r
    simp only [map_mul, rename_C, map_prod, rename_L]
    rw [hc, hp]
  calc
    rename e (numerator rates E) = rename e (∑ a : Fin 3 → Fin n, f a) :=
      congrArg (fun F : P3 => rename e F) hf
    _ = ∑ a : Fin 3 → Fin n, rename e (f a) := by rw [map_sum]
    _ = ∑ a : Fin 3 → Fin n, f (reindex e a) :=
      Finset.sum_congr rfl (fun a _ => hterm a)
    _ = ∑ a : Fin 3 → Fin n, f a := _root_.Equiv.sum_comp (reindex e) f
    _ = numerator rates E := hf.symm

/-- Exact finite denominator identity on its actual regular domain. -/
theorem clear_response_denominators (rates : Fin n → ℝ) (E : Tensor n)
    (s t : ℝ) (hreg : Regular rates s t) :
    MvPolynomial.eval ![s + t, s, t] (numerator rates E) =
      (D rates).eval s * (D rates).eval t * (D rates).eval (s + t) * H rates E s t := by
  classical
  simp only [numerator, map_sum, map_mul, eval_C, eval_L, H, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [eval_D_factor rates i s, eval_D_factor rates j t, eval_D_factor rates k (s + t)]
  field_simp [hreg.1 i, hreg.2.1 j, hreg.2.2 k]


theorem denominator_ne_zero (rates : Fin n → ℝ) (s t : ℝ) (hreg : Regular rates s t) :
    (D rates).eval s * (D rates).eval t * (D rates).eval (s + t) ≠ 0 := by
  classical
  have hd (u : ℝ) (hu : ∀ i, u + rates i ≠ 0) : (D rates).eval u ≠ 0 := by
    simp only [D, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hu i)
  exact mul_ne_zero (mul_ne_zero (hd s hreg.1) (hd t hreg.2.1)) (hd (s + t) hreg.2.2)

/-- Commutes the accepted literal rhoZ with real evaluation. -/
theorem eval_rhoZ (F : P3) (s t : ℝ) :
    MvPolynomial.eval ![s,t] (rhoZ F) = MvPolynomial.eval ![s + t,s,t] F := by
  change MvPolynomial.eval ![s,t]
    (eval₂Hom C ![(X 0 : P2) + X 1, X 0, X 1] F) = _
  rw [coe_eval₂Hom, ← MvPolynomial.eval_assoc]
  have hv : (MvPolynomial.eval ![s,t]) ∘
      (![(X 0 : P2) + X 1, X 0, X 1] : Fin 3 → P2) = ![s + t,s,t] := by
    funext r
    fin_cases r <;> simp
  rw [hv]

/-- A finite-rate positive tail exists even for arbitrary real rates. -/
def tailBound (rates : Fin n → ℝ) : ℝ := 1 + ∑ i, |rates i|

theorem tailBound_pos (rates : Fin n → ℝ) : 0 < tailBound rates := by
  have hs : 0 ≤ ∑ i, |rates i| := Finset.sum_nonneg (fun i _ => abs_nonneg (rates i))
  unfold tailBound
  linarith

theorem tail_regular (rates : Fin n → ℝ) (s t : ℝ)
    (hs : tailBound rates < s) (ht : tailBound rates < t) : Regular rates s t := by
  have hneg (i : Fin n) : -rates i ≤ ∑ j, |rates j| :=
    (neg_le_abs (rates i)).trans (Finset.single_le_sum (fun j _ => abs_nonneg (rates j))
      (Finset.mem_univ i))
  have hs0 := lt_trans (tailBound_pos rates) hs
  refine ⟨?_, ?_, ?_⟩ <;> intro i
  · apply ne_of_gt
    have hi := hneg i
    unfold tailBound at hs
    linarith
  · apply ne_of_gt
    have hi := hneg i
    unfold tailBound at ht
    linarith
  · apply ne_of_gt
    have hi := hneg i
    unfold tailBound at ht
    linarith

/-- Actual positive regular data, with no rate sign or injection assumption,
are equivalent to the polynomial plane identity. -/
theorem ordinary_data_iff_plane (rates : Fin n → ℝ) (E : Tensor n) :
    NullRegular rates E ↔ rhoZ (numerator rates E) = 0 := by
  constructor
  · intro h
    apply MvPolynomial.funext_set (fun _ : Fin 2 => Set.Ioi (tailBound rates))
      (fun _ => Set.Ioi_infinite _)
    intro w hw
    have hs : tailBound rates < w 0 := hw 0 (Set.mem_univ 0)
    have ht : tailBound rates < w 1 := hw 1 (Set.mem_univ 1)
    have hwv : w = ![w 0,w 1] := by funext r; fin_cases r <;> rfl
    rw [hwv, eval_rhoZ, clear_response_denominators rates E _ _ (tail_regular rates _ _ hs ht),
      h _ _ (lt_trans (tailBound_pos rates) hs) (lt_trans (tailBound_pos rates) ht)
        (tail_regular rates _ _ hs ht), mul_zero, map_zero]
  · intro h s t hs ht hreg
    have hz : MvPolynomial.eval ![s + t,s,t] (numerator rates E) = 0 := by
      rw [← eval_rhoZ, h, map_zero]
    rw [clear_response_denominators rates E s t hreg] at hz
    exact (mul_eq_zero.mp hz).resolve_left (denominator_ne_zero rates s t hreg)

theorem positive_regular (rates : Fin n → ℝ) (hpos : ∀ i, 0 < rates i)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) : Regular rates s t := by
  exact ⟨fun i => ne_of_gt (add_pos hs (hpos i)),
    fun i => ne_of_gt (add_pos ht (hpos i)),
    fun i => ne_of_gt (add_pos (add_pos hs ht) (hpos i))⟩

theorem nullPositive_iff_nullRegular (rates : Fin n → ℝ) (hpos : ∀ i, 0 < rates i)
    (E : Tensor n) : NullPositive rates E ↔ NullRegular rates E := by
  exact ⟨fun h s t hs ht _ => h s t hs ht,
    fun h s t hs ht => h s t hs ht (positive_regular rates hpos s t hs ht)⟩

theorem positive_data_iff_plane (rates : Fin n → ℝ) (hpos : ∀ i, 0 < rates i)
    (E : Tensor n) : NullPositive rates E ↔ rhoZ (numerator rates E) = 0 := by
  rw [nullPositive_iff_nullRegular rates hpos, ordinary_data_iff_plane]

theorem H_sub (rates : Fin n → ℝ) (S T : Tensor n) (s t : ℝ) :
    H rates (S - T) s t = H rates S s t - H rates T s t := by
  simp [H, sub_div, Finset.sum_sub_distrib]

theorem sameRegular_iff_plane (rates : Fin n → ℝ) (S T : Tensor n) :
    SameRegular rates S T ↔ rhoZ (numerator rates (S - T)) = 0 := by
  rw [← ordinary_data_iff_plane]
  simp only [SameRegular, NullRegular, H_sub, sub_eq_zero]

theorem samePositive_iff_plane (rates : Fin n → ℝ) (hpos : ∀ i, 0 < rates i)
    (S T : Tensor n) :
    SamePositive rates S T ↔ rhoZ (numerator rates (S - T)) = 0 := by
  rw [← positive_data_iff_plane rates hpos]
  simp only [SamePositive, NullPositive, H_sub, sub_eq_zero]

/-- Accepted factor/degree results and the derived Box force zero in small n. -/
theorem small_n_polynomial_zero (hn : n ≤ 3) (F : P3)
    (hbox : Box n F) (hsym : SymPoly F) (hz : rhoZ F = 0) : F = 0 := by
  by_cases hn0 : n = 0
  · subst n
    exact (box_zero_iff F).mp hbox
  · by_contra hF
    obtain ⟨R, hR⟩ := xi_dvd hsym hz
    have hdeg := factor_degree hR hF 0
    have hlt := (box_iff_degree_lt (Nat.pos_of_ne_zero hn0) F).mp hbox 0
    omega

/-- Actual regular-data injection on unrestricted fully symmetric residual
 tensors for n<=3 (N<=4 after a separately calibrated ground subtraction). -/
theorem small_n_nullRegular (rates : Fin n → ℝ) (hRates : Function.Injective rates)
    (hn : n ≤ 3) (E : Tensor n) (hsym : FullSymTensor E)
    (hdata : NullRegular rates E) : E = 0 := by
  apply (numerator_eq_zero_iff rates hRates E).mp
  exact small_n_polynomial_zero hn _ (numerator_box rates E)
    (numerator_symmetric rates E hsym) ((ordinary_data_iff_plane rates E).mp hdata)

theorem small_n_nullPositive (rates : Fin n → ℝ) (hRates : Function.Injective rates)
    (hpos : ∀ i, 0 < rates i) (hn : n ≤ 3) (E : Tensor n)
    (hsym : FullSymTensor E) (hdata : NullPositive rates E) : E = 0 := by
  exact small_n_nullRegular rates hRates hn E hsym
    ((nullPositive_iff_nullRegular rates hpos E).mp hdata)

theorem fullSymTensor_sub (S T : Tensor n) (hS : FullSymTensor S)
    (hT : FullSymTensor T) : FullSymTensor (S - T) := by
  intro e a
  exact congrArg₂ (· - ·) (hS e a) (hT e a)

theorem small_n_sameRegular (rates : Fin n → ℝ) (hRates : Function.Injective rates)
    (hn : n ≤ 3) (S T : Tensor n) (hS : FullSymTensor S) (hT : FullSymTensor T)
    (hdata : SameRegular rates S T) : S = T := by
  apply sub_eq_zero.mp
  apply small_n_nullRegular rates hRates hn (S - T) (fullSymTensor_sub S T hS hT)
  intro s t hs ht hreg
  rw [H_sub, hdata s t hs ht hreg, sub_self]

theorem small_n_samePositive (rates : Fin n → ℝ) (hRates : Function.Injective rates)
    (hpos : ∀ i, 0 < rates i) (hn : n ≤ 3) (S T : Tensor n)
    (hS : FullSymTensor S) (hT : FullSymTensor T)
    (hdata : SamePositive rates S T) : S = T := by
  apply sub_eq_zero.mp
  apply small_n_nullPositive rates hRates hpos hn (S - T) (fullSymTensor_sub S T hS hT)
  intro s t hs ht
  rw [H_sub, hdata s t hs ht, sub_self]


end C145.H2

end
