/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.Thm1.Count
public import LeanPool.RoyStrongSix.Thm1.Deriv
public import LeanPool.RoyStrongSix.Thm1.Params
public import LeanPool.RoyStrongSix.Thm1.Quot
public import LeanPool.RoyStrongSix.Thm1.Reduce

/-!
# The core of Theorem 1, part 1: points, derivation words, and the obstruction branch

* `PtData`: a point `η ∈ Qbar^{d₀} × 𝓛^{d₁}` together with its `Qbar`-point `exp_G η = (a, α)`.
* `gpt D s = exp_G(Σ sᵢ ηᵢ) = (Σ sᵢ aᵢ, Π αᵢ^{sᵢ})` and `γpt η s = Σ sᵢ ηᵢ`. They satisfy `gsum_gpt`
  (`exp_G` is a homomorphism on the grid) and the relations `gpt_rel1`, `gpt_rel2`.
* `vanishesAlong_of_words`: if `P` vanishes under all derivation *words* over a basis of `W`, it
  vanishes along `W` (multilinearity of `D_{w₁} ⋯ D_{w_r}` in the `wᵢ`).
-/

@[expose] public section

namespace LeanPool

open Module Submodule _root_.MvPolynomial
open StrongSix.Roy

namespace StrongSix.Thm1

variable {d0 d1 ℓ : ℕ}

/-! ### Points -/

/-- A point `η ∈ Qbar^{d₀} × 𝓛^{d₁}` with `exp_G η = (a, α) ∈ G(Qbar)`. -/
structure PtData (d0 d1 : ℕ) (η : E d0 d1) where
  /-- Algebraic additive coordinates mapping to the additive part of the point. -/
  a : Fin d0 → Qb
  /-- Nonzero algebraic coordinates equal to the exponentials of the logarithmic part. -/
  α : Fin d1 → Qbˣ
  ha : incl d0 a = η.1
  hα : ∀ j, algebraMap Qb ℂ (α j : Qb) = Complex.exp (η.2 j)

theorem exists_ptData {η : E d0 d1} (h : AlgVec η.1 ∧ ∀ j, η.2 j ∈ logAlg) :
    Nonempty (PtData d0 d1 η) := by
  obtain ⟨a, ha⟩ := exists_incl_of_algVec h.1
  let e : Fin d1 → Qb := fun j => ⟨Complex.exp (η.2 j), mem_algebraicClosure_iff.mpr (h.2 j)⟩
  have he : ∀ j, e j ≠ 0 := fun j hj => Complex.exp_ne_zero (η.2 j) (congrArg Subtype.val hj)
  exact ⟨⟨a, fun j => Units.mk0 (e j) (he j), ha, fun j => rfl⟩⟩

variable {η : Fin ℓ → E d0 d1} (D : ∀ i, PtData d0 d1 (η i))

/-- `exp_G(Σ sᵢ ηᵢ) = (Σ sᵢ aᵢ, Π αᵢ^{sᵢ})`. -/
noncomputable def gpt (s : Fin ℓ → ℕ) : GPt Qb d0 d1 := (∑ i, s i • (D i).a, ∏ i, (D i).α ^ s i)

/-- `Σ sᵢ ηᵢ`. -/
noncomputable def γpt (η : Fin ℓ → E d0 d1) (s : Fin ℓ → ℕ) : E d0 d1 := ∑ i, (s i : ℂ) • η i

theorem gpt_rel1 (s : Fin ℓ → ℕ) (k : Fin d0) :
    algebraMap Qb ℂ ((gpt D s).1 k) = (γpt η s).1 k := by
  simp only [gpt, γpt, Finset.sum_apply, Prod.fst_sum, Prod.smul_fst, Pi.smul_apply, map_sum,
    nsmul_eq_mul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← (D i).ha]; rfl

theorem gpt_rel2 (s : Fin ℓ → ℕ) (j : Fin d1) :
    algebraMap Qb ℂ ((gpt D s).2 j : Qb) = Complex.exp ((γpt η s).2 j) := by
  simp only [gpt, γpt, Finset.prod_apply, Pi.pow_apply, Units.coe_prod, Units.val_pow_eq_pow_val,
    map_prod, map_pow, (D _).hα, Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Complex.exp_nat_mul]

theorem gpt_zero : gpt D 0 = GPt.zero := by
  simp [gpt, GPt.zero]

/-- `exp_G` is a homomorphism on the grid. -/
theorem gsum_gpt {k : ℕ} (s : Fin k → Fin ℓ → ℕ) : gsum (fun m => gpt D (s m)) = gpt D (∑ m, s
  m) := by
  simp only [gsum, gpt]
  refine Prod.ext ?_ ?_
  · simp only [Finset.sum_apply, Finset.sum_smul]
    exact Finset.sum_comm
  · simp only [Finset.sum_apply]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_pow_eq_pow_sum]

/-! ### Derivation words -/

section Words

variable {K : Type*} [Field K]

theorem invDer_add_left (w w' : LieG K d0 d1) (P : MvPolynomial (Var d0 d1) K) :
    invDer (w + w') P = invDer w P + invDer w' P := by
  simp only [invDer, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  abel

theorem invDer_smul_left (c : K) (w : LieG K d0 d1) (P : MvPolynomial (Var d0 d1) K) :
    invDer (c • w) P = c • invDer w P := by
  simp only [invDer, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
    Finset.smul_sum, smul_add]

theorem invDer_smul_right (w : LieG K d0 d1) (c : K) (P : MvPolynomial (Var d0 d1) K) :
    invDer w (c • P) = c • invDer w P := by
  simp only [invDer, Derivation.map_smul, mul_smul_comm, Finset.smul_sum, smul_add]
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _

/-- The span of the derivation words of length `k` over the family `wb`. -/
noncomputable def wordSpan {t : ℕ} (wb : Fin t → LieG K d0 d1) (P : MvPolynomial (Var d0 d1) K)
  (k : ℕ) :
    Submodule K (MvPolynomial (Var d0 d1) K) :=
  span K {Q | ∃ word : List (Fin t), word.length = k ∧ Q = invDers (word.map wb) P}

theorem invDer_mem_wordSpan {t : ℕ} (wb : Fin t → LieG K d0 d1) (P : MvPolynomial (Var d0 d1) K)
    {k : ℕ} {w : LieG K d0 d1} (hw : w ∈ span K (Set.range wb)) {Q : MvPolynomial (Var d0 d1) K}
    (hQ : Q ∈ wordSpan wb P k) : invDer w Q ∈ wordSpan wb P (k + 1) := by
  obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun K).mp hw
  -- linearity in `w`
  have hlin : ∀ Q', invDer (∑ j, c j • wb j) Q' = ∑ j, c j • invDer (wb j) Q' := by
    intro Q'
    induction (Finset.univ : Finset (Fin t)) using Finset.induction_on with
    | empty => simp [invDer]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, invDer_add_left, invDer_smul_left, ih]
  rw [hlin]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
  -- `Q ↦ D_{wb j} Q` maps the words of length `k` into those of length `k + 1`
  induction hQ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨word, hlen, rfl⟩ := hx
    exact subset_span ⟨j :: word, by simp [hlen], rfl⟩
  | zero => simp [invDer]
  | add x y _ _ hx hy => rw [invDer_add]; exact add_mem hx hy
  | smul a x _ hx => rw [invDer_smul_right]; exact Submodule.smul_mem _ _ hx

theorem invDers_mem_wordSpan {t : ℕ} (wb : Fin t → LieG K d0 d1) (P : MvPolynomial (Var d0 d1) K)
    (l : List (LieG K d0 d1)) (hl : ∀ w ∈ l, w ∈ span K (Set.range wb)) :
    invDers l P ∈ wordSpan wb P l.length := by
  induction l with
  | nil => exact subset_span ⟨[], rfl, rfl⟩
  | cons w l ih =>
    rw [invDers_cons, List.length_cons]
    exact invDer_mem_wordSpan wb P (hl w List.mem_cons_self)
      (ih fun w' hw' => hl w' (List.mem_cons_of_mem _ hw'))

/-- **Vanishing on basis words implies vanishing along `W`.** -/
theorem vanishesAlong_of_words {t : ℕ} (W : Submodule K (LieG K d0 d1))
    (wb : Fin t → LieG K d0 d1) (hW : W = span K (Set.range wb)) (P : MvPolynomial (Var d0 d1) K)
    (k : ℕ) (g : GPt K d0 d1)
    (h : ∀ word : List (Fin t), word.length < k → eval g.coords (invDers (word.map wb) P) = 0) :
    VanishesAlong W P k g := by
  intro l hl hlen
  have hmem := invDers_mem_wordSpan wb P l (fun w hw => hW ▸ hl w hw)
  let ev : MvPolynomial (Var d0 d1) K →ₗ[K] K := (MvPolynomial.aeval g.coords).toLinearMap
  have hle : wordSpan wb P l.length ≤ LinearMap.ker ev := by
    rw [wordSpan, span_le]
    rintro _ ⟨word, hw, rfl⟩
    change MvPolynomial.eval g.coords (invDers (word.map wb) P) = 0
    exact h word (hw ▸ hlen)
  have := hle hmem
  rw [LinearMap.mem_ker] at this
  exact this

end Words

/-! ### The obstruction branch -/

/-- Independence modulo `Ω'` forces injective indices. -/
theorem idx_injective {k0 k1 ρ : ℕ} (s : E d0 d1 →ₗ[ℂ] E k0 k1) (idx : Fin ρ → Fin ℓ)
    (hidx : ∀ c : Fin ρ → ℚ, (∑ k, c k • s (η (idx k))) ∈ Omega k0 k1 → c = 0) :
    Function.Injective idx := by
  classical
  intro k k' hkk
  by_contra hne
  have h := hidx (Pi.single k 1 - Pi.single k' 1) (by
    have : (∑ m, (Pi.single k (1 : ℚ) - Pi.single k' 1 : Fin ρ → ℚ) m • s (η (idx m))) = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, Pi.single_apply, ite_smul,
        one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hkk, sub_self]
    rw [this]; exact zero_mem _)
  have := congrFun h k
  simp [Ne.symm hne] at this

/-- The grid vector with `a` in the coordinates `idx`. -/
def spread {ρ : ℕ} (idx : Fin ρ → Fin ℓ) (a : Fin ρ → ℕ) : Fin ℓ → ℕ :=
  fun i => ∑ k, if idx k = i then a k else 0

theorem spread_le {ρ S : ℕ} {idx : Fin ρ → Fin ℓ} (hinj : Function.Injective idx)
    {a : Fin ρ → ℕ} (ha : ∀ k, a k ≤ S) (i : Fin ℓ) : spread idx a i ≤ S := by
  classical
  unfold spread
  by_cases h : ∃ k, idx k = i
  · obtain ⟨k, rfl⟩ := h
    rw [Finset.sum_eq_single k (fun k' _ hk' => by
        simp only [show idx k' ≠ idx k from fun e => hk' (hinj e), ↓reduceIte])
      (fun hk => absurd (Finset.mem_univ k) hk)]
    simp only [↓reduceIte]
    exact ha k
  · push Not at h
    simp [h]

theorem γpt_spread {ρ : ℕ} (idx : Fin ρ → Fin ℓ) (a : Fin ρ → ℕ) :
    γpt η (spread idx a) = ∑ k, (a k : ℂ) • η (idx k) := by
  classical
  simp only [γpt, spread, Nat.cast_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Nat.cast_ite, Nat.cast_zero, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]

/-- `ρ' = dim s(Y) − dim (s(Y) ∩ Ω')`. -/
noncomputable def rho' {k0 k1 : ℕ} (η : Fin ℓ → E d0 d1) (s : E d0 d1 →ₗ[ℂ] E k0 k1) : ℕ :=
  finrank ℚ ((span ℚ (Set.range η)).map (s.restrictScalars ℚ)) -
    finrank ℚ ↥((span ℚ (Set.range η)).map (s.restrictScalars ℚ) ⊓ Omega k0 k1)

/-- A finite grid contains as many inequivalent points as the rank modulo periods permits. -/
theorem exists_separated_grid {k0 k1 : ℕ} (η : Fin ℓ → E d0 d1)
    (D : ∀ i, PtData d0 d1 (η i)) (h0 : Submodule Qb (Fin d0 → Qb))
    (U : Submodule ℚ (Fin d1 → ℚ)) (s : E d0 d1 →ₗ[ℂ] E k0 k1)
    (compatible : ∀ a b, EquivMod h0 U (gpt D a) (gpt D b) →
      s (γpt η a - γpt η b) ∈ Omega k0 k1) (S' : ℕ) :
    ∃ F : Finset (GPt Qb d0 d1),
      F ⊆ (Fintype.piFinset fun _ : Fin ℓ => Finset.range (S' + 1)).image (gpt D) ∧
      (∀ g ∈ F, ∀ g' ∈ F, EquivMod h0 U g g' → g = g') ∧
      (F.card : ℝ) = ((S' : ℝ) + 1) ^ rho' η s := by
  classical
  let grid := Fintype.piFinset fun _ : Fin ℓ => Finset.range (S' + 1)
  let Sg := grid.image (gpt D)
  -- the inequivalent points
  obtain ⟨idx, hidx⟩ := exists_indep_mod_Omega η s
  have hinj := idx_injective s idx hidx
  set ρ := rho' η s
  let pt : (Fin ρ → Fin (S' + 1)) → GPt Qb d0 d1 := fun a => gpt D (spread idx fun k => a k)
  have hequiv : ∀ a b, EquivMod h0 U (pt a) (pt b) → a = b := by
    intro a b hab
    have h1 := compatible (spread idx fun k => a k) (spread idx fun k => b k) hab
    rw [γpt_spread, γpt_spread] at h1
    have := eq_of_sub_mem_Omega η s idx hidx (fun k => a k) (fun k => b k) h1
    funext k
    exact Fin.ext (congrFun this k)
  have hrefl : ∀ g : GPt Qb d0 d1, EquivMod h0 U g g := fun g =>
    ⟨by simp, fun φ _ => by simp⟩
  have hptinj : Function.Injective pt := fun a b h => hequiv a b (h ▸ hrefl (pt a))
  set F : Finset (GPt Qb d0 d1) := Finset.univ.image pt with hF
  have hFS : F ⊆ Sg := by
    intro g hg
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hg
    refine Finset.mem_image.mpr ⟨_, Fintype.mem_piFinset.mpr fun i => ?_, rfl⟩
    have := spread_le hinj (a := fun k => (a k : ℕ)) (S := S') (fun k => Nat.lt_succ_iff.mp (a
      k).2) i
    simpa [Nat.lt_succ_iff] using this
  have hFin : ∀ g ∈ F, ∀ g' ∈ F, EquivMod h0 U g g' → g = g' := by
    intro g hg g' hg' he
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hg'
    rw [hequiv a b he]
  have hcard : (F.card : ℝ) = ((S' : ℝ) + 1) ^ ρ := by
    rw [hF, Finset.card_image_of_injective _ hptinj, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin]
    push_cast; ring
  exact ⟨F, hFS, hFin, hcard⟩

/-- **The obstruction branch.** A non-zero `P` vanishing along `W_K` on the grid `exp_G Γ(d S')`
yields `(h₀, U)` with
`T^{dim s(W)} (S'+1)^{ρ'} L₀^{dim h₀} L₁^{d₁ − dim U} ≤ C L₀^{d₀} L₁^{d₁}`. -/
theorem obstruction (hM : MultEst Qb) (d0 d1 : ℕ) :
    ∃ C : ℝ, ∀ (W : Submodule ℂ (E d0 d1)), RationalOverQbar W →
      ∀ {ℓ : ℕ} (η : Fin ℓ → E d0 d1) (D : ∀ i, PtData d0 d1 (η i))
        (P : MvPolynomial (Var d0 d1) Qb) (T L0 L1 S' : ℕ),
      P ≠ 0 → BidegLE P L0 L1 → 1 ≤ T → 1 ≤ L0 → 1 ≤ L1 →
      (∀ s : Fin ℓ → ℕ, (∀ i, s i ≤ (d0 + d1) * S') →
        VanishesAlong (WK W) P ((d0 + d1) * T + 1) (gpt D s)) →
      ∃ (h0 : Submodule Qb (Fin d0 → Qb)) (U : Submodule ℚ (Fin d1 → ℚ)),
        (h0 ≠ ⊤ ∨ U ≠ ⊥) ∧
        (T : ℝ) ^ finrank ℂ ↥(W.map (sMap h0 U)) * ((S' : ℝ) + 1) ^ rho' η (sMap h0 U) *
            (L0 : ℝ) ^ finrank Qb ↥h0 * (L1 : ℝ) ^ (d1 - finrank ℚ ↥U) ≤
          C * (L0 : ℝ) ^ d0 * (L1 : ℝ) ^ d1 := by
  classical
  obtain ⟨C, hC⟩ := hM d0 d1
  refine ⟨C, fun W hW ℓ η D P T L0 L1 S' hP hbid hT hL0 hL1 hvan => ?_⟩
  -- the grid `exp_G Γ(S')`
  set grid : Finset (Fin ℓ → ℕ) := Fintype.piFinset fun _ => Finset.range (S' + 1) with hgrid
  set Sg : Finset (GPt Qb d0 d1) := grid.image (gpt D) with hSg
  have hS0 : GPt.zero ∈ Sg :=
    Finset.mem_image.mpr ⟨0, Fintype.mem_piFinset.mpr fun _ => by simp, gpt_zero D⟩
  have hsum : ∀ σ : Fin (d0 + d1) → GPt Qb d0 d1, (∀ i, σ i ∈ Sg) →
      VanishesAlong (WK W) P ((d0 + d1) * T + 1) (gsum σ) := by
    intro σ hσ
    choose sv hsv hσeq using fun i => Finset.mem_image.mp (hσ i)
    have hσ' : σ = fun m => gpt D (sv m) := funext fun m => (hσeq m).symm
    rw [hσ', gsum_gpt]
    refine hvan _ fun i => ?_
    have hle : ∀ m, sv m i ≤ S' := fun m => by
      have := Fintype.mem_piFinset.mp (hsv m) i
      simpa [Nat.lt_succ_iff] using this
    calc (∑ m, sv m) i = ∑ m, sv m i := Finset.sum_apply _ _ _
      _ ≤ ∑ _m : Fin (d0 + d1), S' := Finset.sum_le_sum fun m _ => hle m
      _ = (d0 + d1) * S' := by simp
  obtain ⟨h0, U, hnd, hineq⟩ := hC (WK W) Sg P T L0 L1 hS0 hP hbid hT hL0 hL1 hsum
  refine ⟨h0, U, hnd, ?_⟩
  obtain ⟨F, hFS, hFin, hcard⟩ := exists_separated_grid η D h0 U (sMap h0 U)
    (fun a b hab => sMap_sub_mem_Omega h0 U (γpt η a) (γpt η b)
      (gpt D a) (gpt D b) (gpt_rel1 D _) (gpt_rel2 D _)
      (gpt_rel1 D _) (gpt_rel2 D _) hab) S'
  have h := hineq F hFS hFin
  rw [hcard, ← finrank_map_sMap h0 U W hW] at h
  exact h

/-- A uniform multiplicative power bound forces the corresponding exponent inequality. -/
theorem exponents_le_of_power_bound (X : Params.Exps) (hn : 1 ≤ X.n)
    {d0 d1 h u c ρ β : ℕ} {C : ℝ} (hh : h ≤ d0) (hu : u ≤ d1)
    (hβ : C < β) (hβ1 : 1 ≤ β)
    (hineq : ((β ^ (X.n * X.θ) : ℕ) : ℝ) ^ c *
        (((β ^ (X.n * X.σ) : ℕ) : ℝ) + 1) ^ ρ *
        ((β ^ (X.n * X.Q) : ℕ) : ℝ) ^ h *
        ((β ^ (X.n * X.x1) : ℕ) : ℝ) ^ (d1 - u) ≤
      C * ((β ^ (X.n * X.Q) : ℕ) : ℝ) ^ d0 * ((β ^ (X.n * X.x1) : ℕ) : ℝ) ^ d1) :
    c * X.θ + ρ * X.σ ≤ (d0 - h) * X.Q + u * X.x1 := by
  by_contra hcon
  push Not at hcon
  have hb1 : (1 : ℝ) ≤ (β : ℝ) := by exact_mod_cast hβ1
  have hb0 : (0 : ℝ) < (β : ℝ) := by linarith
  set A := X.n * X.θ * c + X.n * X.σ * ρ + X.n * X.Q * h +
    X.n * X.x1 * (d1 - u) with hA
  set B := X.n * X.Q * d0 + X.n * X.x1 * d1 with hB
  have hAB : B + 1 ≤ A := by
    have h1 := Nat.mul_le_mul_left X.n (Nat.succ_le_of_lt hcon)
    have e0 : d0 = (d0 - h) + h := (Nat.sub_add_cancel hh).symm
    have e1 : d1 = u + (d1 - u) := (Nat.add_sub_cancel' hu).symm
    have eB : B = X.n * ((d0 - h) * X.Q + u * X.x1) +
        X.n * X.Q * h + X.n * X.x1 * (d1 - u) := by
      rw [hB]; conv_lhs => rw [e0, e1]
      ring
    have eA : A = X.n * (c * X.θ + ρ * X.σ) + X.n * X.Q * h +
        X.n * X.x1 * (d1 - u) := by
      rw [hA]; ring
    rw [eA, eB]
    have : X.n * ((d0 - h) * X.Q + u * X.x1) + X.n ≤
        X.n * (c * X.θ + ρ * X.σ) := by
      simpa [Nat.mul_succ] using h1
    omega
  have hlow : (β : ℝ) ^ A ≤ C * (β : ℝ) ^ B := by
    have e1 : ((β : ℝ) ^ A) ≤ ((β ^ (X.n * X.θ) : ℕ) : ℝ) ^ c *
        (((β ^ (X.n * X.σ) : ℕ) : ℝ) + 1) ^ ρ * ((β ^ (X.n * X.Q) : ℕ) : ℝ) ^ h *
        ((β ^ (X.n * X.x1) : ℕ) : ℝ) ^ (d1 - u) := by
      push_cast
      rw [hA]
      simp only [pow_add, pow_mul]
      refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left ?_ (by positivity)) le_rfl
        (by positivity) (by positivity)) le_rfl (by positivity) (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have e2 : C * ((β ^ (X.n * X.Q) : ℕ) : ℝ) ^ d0 * ((β ^ (X.n * X.x1) : ℕ) : ℝ) ^ d1 =
        C * (β : ℝ) ^ B := by
      push_cast
      rw [hB, pow_add, pow_mul, pow_mul]
      ring
    exact e1.trans (hineq.trans_eq e2)
  have hup : (β : ℝ) * (β : ℝ) ^ B ≤ (β : ℝ) ^ A := by
    rw [← pow_succ']
    exact pow_le_pow_right₀ hb1 hAB
  have hpos : (0 : ℝ) < (β : ℝ) ^ B := by positivity
  nlinarith

/-- **From the obstruction to the conclusion of Theorem 1.** With the parameters
`T = β^{nθ}`, `S' = β^{nσ}`, `L₀ = β^{nQ}`, `L₁ = β^{n x₁}` and `β > C`, the inequality of
`obstruction` forces the integer inequality `cθ + ρσ ≤ d₀'Q + d₁'x₁`, and then
`ratio_of_obstruction` gives the ratio bound. -/
theorem concl_of_obstruction {Y : Submodule ℚ (E d0 d1)} {W V : Submodule ℂ (E d0 d1)}
    (H : Hyps d0 d1 Y W V) (η : Fin ℓ → E d0 d1) (hηY : span ℚ (Set.range η) = Y)
    (X : Params.Exps) (hXp : X.p = d1) (hXd : X.d = d0 + d1) (_ : X.n = finrank ℂ ↥V)
    (hXq : X.q = d0 + d1 - finrank ℂ ↥V) (hqp : X.q ≤ X.p) (hn : 1 ≤ X.n)
    {C : ℝ} {β : ℕ} (hβ : C < β) (hβ1 : 1 ≤ β)
    (h0 : Submodule Qb (Fin d0 → Qb)) (U : Submodule ℚ (Fin d1 → ℚ)) (hnd : h0 ≠ ⊤ ∨ U ≠ ⊥)
    (hineq : ((β ^ (X.n * X.θ) : ℕ) : ℝ) ^ finrank ℂ ↥(W.map (sMap h0 U)) *
        (((β ^ (X.n * X.σ) : ℕ) : ℝ) + 1) ^ rho' η (sMap h0 U) *
        ((β ^ (X.n * X.Q) : ℕ) : ℝ) ^ finrank Qb ↥h0 *
        ((β ^ (X.n * X.x1) : ℕ) : ℝ) ^ (d1 - finrank ℚ ↥U) ≤
      C * ((β ^ (X.n * X.Q) : ℕ) : ℝ) ^ d0 * ((β ^ (X.n * X.x1) : ℕ) : ℝ) ^ d1) :
    T1Concl d0 d1 Y W ((d1 : ℚ) / ((d0 + d1 : ℚ) - finrank ℂ ↥V)) := by
  have hsurj := sMap_surjective h0 U
  have halg := sMap_alg h0 U
  have hrat := sMap_rat h0 U
  generalize sMap h0 U = s at hsurj halg hrat hineq
  have hf0le : finrank Qb ↥h0 ≤ d0 := by
    have := Submodule.finrank_le h0; simpa using this
  have hd1le : finrank ℚ ↥U ≤ d1 := by
    have := Submodule.finrank_le U; simpa using this
  have hVlt := finrank_lt_of_ne_top H.Vne
  set c := finrank ℂ ↥(W.map s) with hc
  set ρ := rho' η s with hρ
  -- the integer inequality
  have hob := exponents_le_of_power_bound X hn hf0le hd1le hβ hβ1 hineq
  -- the ratio bound
  have hd' : 1 ≤ (d0 - finrank Qb ↥h0) + finrank ℚ ↥U := by
    rcases hnd with h | h
    · have : finrank Qb ↥h0 < d0 := by
        have := Submodule.finrank_lt h; simpa using this
      omega
    · have : finrank ℚ ↥U ≠ 0 := fun h' => h (Submodule.finrank_eq_zero.mp h')
      omega
  obtain ⟨hcd, hratio⟩ := X.ratio_of_obstruction hqp hd' (by rw [hXd]; omega) hob
  refine ⟨d0 - finrank Qb ↥h0, finrank ℚ ↥U, s, hsurj, halg, hrat, ne_top_of_finrank_lt hcd, ?_⟩
  -- unfold the left side
  have hfd : FiniteDimensional ℚ ↥((span ℚ (Set.range η)).map (s.restrictScalars ℚ)) := by
    rw [Submodule.map_span]
    exact FiniteDimensional.span_of_finite ℚ ((Set.finite_range η).image _)
  have hab : finrank ℚ ↥((span ℚ (Set.range η)).map (s.restrictScalars ℚ) ⊓
      Omega (d0 - finrank Qb ↥h0) (finrank ℚ ↥U)) ≤
      finrank ℚ ↥((span ℚ (Set.range η)).map (s.restrictScalars ℚ)) :=
    Submodule.finrank_mono inf_le_left
  have hnum : ((finrank ℚ ↥U : ℕ) : ℚ) - finrank ℚ ↥((span ℚ (Set.range η)).map
      (s.restrictScalars ℚ) ⊓ Omega (d0 - finrank Qb ↥h0) (finrank ℚ ↥U)) +
      finrank ℚ ↥((span ℚ (Set.range η)).map (s.restrictScalars ℚ)) =
      (finrank ℚ ↥U : ℚ) + ρ := by
    rw [hρ, rho', Nat.cast_sub hab]; ring
  unfold lhs
  rw [← hηY, hnum, ← hc]
  have hden1 : (0 : ℚ) < ((d0 - finrank Qb ↥h0 : ℕ) : ℚ) + (finrank ℚ ↥U : ℚ) - c := by
    have : (c : ℚ) < ((d0 - finrank Qb ↥h0 : ℕ) : ℚ) + (finrank ℚ ↥U : ℚ) := by
      exact_mod_cast hcd
    linarith
  have hden2 : (0 : ℚ) < (d0 + d1 : ℚ) - finrank ℂ ↥V := by
    have : (finrank ℂ ↥V : ℚ) < d0 + d1 := by exact_mod_cast hVlt
    linarith
  rw [div_le_div_iff₀ hden1 hden2]
  have hr := hratio
  rw [hXq, hXp] at hr
  have hr' := (Nat.cast_le (α := ℚ)).mpr hr
  push_cast [Nat.cast_sub hVlt.le, Nat.cast_sub hcd.le] at hr'
  linarith
end StrongSix.Thm1

end LeanPool
