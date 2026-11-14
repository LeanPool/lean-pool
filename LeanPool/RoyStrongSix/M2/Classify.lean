/-
Copyright (c) 2026 Shawn Krisman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shawn Krisman
-/
module

public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Ring
public import LeanPool.RoyStrongSix.M2.Geom

/-!
# Algebraic subgroups of `G_a^{d₀} × G_m^{d₁}` (Roy, DALAG Prop. 5.6)

For a subset `E` of `G`:
* `linV E` is the subspace cut out by the linear forms that vanish on `E_x`;
* `latt E` is the lattice of `λ ∈ ℤ^{d₁}` with `y^λ = 1` on `E`;
* `prodSet V Λ = V × T_Λ`.

**`classify`**: an algebraic subgroup `E` (a subgroup that is the zero set of polynomials) equals
`linV E × T_{latt E}`. For `x ∈ V`, write `P(x, y, y⁻¹) = Σ_γ A_γ(L x) y^γ`, with `γ` ranging over
representatives of `ℤ^{d₁}/Λ` and `L` coordinates on `V`. Then apply `expPoly_indep_subgroup`.
-/

@[expose] public section

namespace LeanPool

open _root_.MvPolynomial Module StrongSix.Thm1

namespace StrongSix.M2

variable {K : Type*} [Field K] [CharZero K] {d0 d1 : ℕ}

omit [CharZero K] in
theorem chr_zero (y : Fin d1 → Kˣ) : chr y (0 : Fin d1 → ℤ) = 1 := by simp [chr]

/-- The lattice of characters trivial on `E`. -/
def latt (E : Set (GPt K d0 d1)) : AddSubgroup (Fin d1 → ℤ) where
  carrier := {l | ∀ g ∈ E, chr g.2 l = 1}
  add_mem' {a b} ha hb g hg := by rw [chr_add, ha g hg, hb g hg, one_mul]
  zero_mem' g _ := chr_zero g.2
  neg_mem' {a} ha g hg := by
    have h := chr_add g.2 (-a) a
    rw [neg_add_cancel, chr_zero, ha g hg, mul_one] at h
    exact h.symm

/-- The subspace cut out by the linear forms vanishing on `E_x`. -/
def linV (E : Set (GPt K d0 d1)) : Submodule K (Fin d0 → K) where
  carrier := {x | ∀ μ : (Fin d0 → K) →ₗ[K] K, (∀ g ∈ E, μ g.1 = 0) → μ x = 0}
  add_mem' ha hb μ hμ := by rw [map_add, ha μ hμ, hb μ hμ, add_zero]
  zero_mem' μ _ := map_zero μ
  smul_mem' c x hx μ hμ := by rw [map_smul, hx μ hμ, smul_zero]

/-- `V × T_Λ`. -/
def prodSet (V : Submodule K (Fin d0 → K)) (Λ : AddSubgroup (Fin d1 → ℤ)) : Set (GPt K d0 d1) :=
  {g | g.1 ∈ V ∧ ∀ l ∈ Λ, chr g.2 l = 1}

omit [CharZero K] in
theorem subset_prodSet (E : Set (GPt K d0 d1)) : E ⊆ prodSet (linV E) (latt E) :=
  fun g hg => ⟨fun _ hμ => hμ g hg, fun _ hl => hl g hg⟩

omit [CharZero K] in
theorem chr_eq_of_sub_mem {Λ : AddSubgroup (Fin d1 → ℤ)} {y : Fin d1 → Kˣ}
    (hy : ∀ l ∈ Λ, chr y l = 1) {a b : Fin d1 → ℤ} (h : -a + b ∈ Λ) : chr y a = chr y b := by
  have := chr_add y a (-a + b)
  rw [add_neg_cancel_left, hy _ h, mul_one] at this
  exact this.symm

/-- **Roy, Prop. 5.6.** An algebraic subgroup of `G` is `V × T_Λ`. -/
theorem classify {E : Set (GPt K d0 d1)} (hE : IsSubgroupG E)
    {Ps : Set (MvPolynomial (V3 d0 d1) K)} (hzero : E = zeros Ps) :
    E = prodSet (linV E) (latt E) := by
  classical
  apply le_antisymm (subset_prodSet E)
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  rw [hzero]
  intro P hP
  -- coordinates on `V`
  set V := linV E
  set s := finrank K V
  let bV := Module.finBasis K V
  have hLex : ∀ i : Fin s, ∃ Li : (Fin d0 → K) →ₗ[K] K, Li.comp V.subtype = bV.coord i :=
    fun i => LinearMap.exists_extend _
  choose Li hLi using hLex
  let L : (Fin d0 → K) →ₗ[K] (Fin s → K) := LinearMap.pi Li
  have hLb : ∀ i k, L (bV k : Fin d0 → K) i = if k = i then 1 else 0 := by
    intro i k
    have := congrArg (fun f => f (bV k)) (hLi i)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    simp only [L, LinearMap.pi_apply, this, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
  have hxV : ∀ x' ∈ V, x' = ∑ i, L x' i • (bV i : Fin d0 → K) := by
    intro x' hx'
    have h1 : (⟨x', hx'⟩ : V) = ∑ i, bV.repr ⟨x', hx'⟩ i • bV i := (bV.sum_repr _).symm
    have h2 := congrArg Subtype.val h1
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    convert h2 using 3 with i
    have := congrArg (fun f => f ⟨x', hx'⟩) (hLi i)
    simpa [L] using this
  -- `L(E_x)` spans
  have hspan : Submodule.span K ((fun g : GPt K d0 d1 => L g.1) '' E) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ, hφker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    apply hφ
    ext i
    have hμ : ∀ g ∈ E, (φ.comp L) g.1 = 0 := fun g hg =>
      hφker (Submodule.subset_span ⟨g, hg, rfl⟩)
    have := (bV i).2 (φ.comp L) hμ
    simp only [LinearMap.comp_apply] at this
    have hLbi : L (bV i : Fin d0 → K) = Pi.single i 1 := by
      funext j; rw [hLb]; simp [Pi.single_apply, eq_comm]
    simpa [hLbi] using this
  -- representatives of `ℤ^{d₁} / Λ`
  let Λ := latt E
  let rep : (Fin d1 → ℤ) → (Fin d1 → ℤ) := fun v => Quotient.out (QuotientAddGroup.mk v : (Fin
    d1 → ℤ) ⧸ Λ)
  have hrep : ∀ v, (QuotientAddGroup.mk (rep v) : (Fin d1 → ℤ) ⧸ Λ) = QuotientAddGroup.mk v :=
    fun v => Quotient.out_eq _
  have hchr : ∀ {y' : Fin d1 → Kˣ}, (∀ l ∈ Λ, chr y' l = 1) → ∀ v, chr y' v = chr y' (rep v) :=
    fun hy' v => chr_eq_of_sub_mem hy' (QuotientAddGroup.eq.mp (hrep v).symm)
  -- the expansion
  let δ : (V3 d0 d1 →₀ ℕ) → Fin d1 → ℤ :=
    fun m j => (m (Sum.inr (Sum.inl j)) : ℤ) - m (Sum.inr (Sum.inr j))
  let Qm : (V3 d0 d1 →₀ ℕ) → MvPolynomial (Fin s) K :=
    fun m => ∏ k, (∑ i, C ((bV i : Fin d0 → K) k) * X i) ^ m (Sum.inl k)
  have hQm : ∀ x' ∈ V, ∀ m, eval (L x') (Qm m) = ∏ k, x' k ^ m (Sum.inl k) := by
    intro x' hx' m
    simp only [Qm, map_prod, map_pow, map_sum, map_mul, eval_C, eval_X]
    refine Finset.prod_congr rfl fun k _ => ?_
    congr 1
    have e := congrFun (hxV x' hx').symm k
    rw [← e]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  let Γ := P.support.image fun m => rep (δ m)
  let A : (Fin d1 → ℤ) → MvPolynomial (Fin s) K :=
    fun γ => ∑ m ∈ P.support.filter (fun m => rep (δ m) = γ), C (P.coeff m) * Qm m
  have hexp : ∀ g : GPt K d0 d1, g.1 ∈ V → (∀ l ∈ Λ, chr g.2 l = 1) →
      eval (pt g) P = ∑ γ ∈ Γ, eval (L g.1) (A γ) * chr g.2 γ := by
    intro g hg1 hg2
    rw [eval_pt]
    symm
    simp only [A, map_sum, Finset.sum_mul]
    have hfib := Finset.sum_fiberwise_of_maps_to (s := P.support) (t := Γ)
      (g := fun m => rep (δ m)) (fun m hm => Finset.mem_image_of_mem (fun m => rep (δ m)) hm)
      (fun m => eval (L g.1) (C (P.coeff m) * Qm m) * chr g.2 (rep (δ m)))
    trans ∑ m ∈ P.support, eval (L g.1) (C (P.coeff m) * Qm m) * chr g.2 (rep (δ m))
    · rw [← hfib]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i hi => ?_
      rw [(Finset.mem_filter.mp hi).2]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul, eval_C, hQm g.1 hg1, ← hchr hg2]
      ring
  -- the coefficients vanish
  have hA : ∀ γ ∈ Γ, A γ = 0 := by
    apply expPoly_indep_subgroup hE.toSubmonoidG L hspan Γ A id
    · intro i hi j hj hij
      by_contra hcon
      push Not at hcon
      simp only [id] at hcon
      apply hij
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hj
      have hab : -rep (δ a) + rep (δ b) ∈ Λ := fun g hg => by
        rw [chr_add, ← hcon g hg, ← chr_add, neg_add_cancel, chr_zero]
      have : (QuotientAddGroup.mk (rep (δ a)) : (Fin d1 → ℤ) ⧸ Λ) = QuotientAddGroup.mk (rep (δ
        b)) :=
        QuotientAddGroup.eq.mpr hab
      rw [hrep, hrep] at this
      simp only [rep, this]
    · intro g hg
      have := hexp g ((subset_prodSet E hg).1) ((subset_prodSet E hg).2)
      simp only [id]
      rw [← this]
      have hgz : g ∈ zeros Ps := hzero ▸ hg
      exact hgz P hP
  rw [hexp (x, y) hx hy]
  exact Finset.sum_eq_zero fun γ hγ => by rw [hA γ hγ, map_zero, zero_mul]

end StrongSix.M2

end LeanPool
