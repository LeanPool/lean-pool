/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Sobolev.SobolevTriebelLizorkin
public import LeanPool.FunctionSpaces.ApproximationSpaces.Interpolation.ApproxSpaces

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Sobolev spaces on `V` and real interpolation

Let `V` have dimension `n ≥ 1`, `1 < p < ∞` and `m ≥ 1`.  The **grid norm** of `W^m_p(V)` is
`‖f‖_p + inf ∑_α ‖g_α‖_p`, the infimum over the families of weak derivatives
`g_α = ∂_{e_{α_0}} ⋯ ∂_{e_{α_{m-1}}} f` along the basis `e` of `Rd.gridBasis`
(`Rd.sobolevGridNorm`).  Weak derivatives are unique, so the grid norm is
`‖f‖_p + ∑_α ‖∂^{e_α} f‖_p` whenever these derivatives exist (`Rd.sobolevGridNorm_eq`), and it is
finite exactly on `W^m_p(V)` (`Rd.sobolevGridNorm_lt_top_iff`).  It lies between the dyadic
quasi-norms of the Besov spaces `B^m_{p,max(p,2)}` and `B^m_{p,min(p,2)}`, with the named
constants `Rd.approxSobolevGridConst` and `Rd.sobolevGridApproxConst`
(`Rd.approxNormDyadic_le_sobolevGridNorm`, `Rd.sobolevGridNorm_le_approxNormDyadic`), so the
sandwich principle gives, for `0 < θ, η < 1` and `1 ≤ q ≤ ∞`,

`(L_p, W^m_p)_{θ,q} = B^{θm}_{p,q}` (`Rd.memKMethod_lpSobolevCouple_iff`) and
`(W^{m₀}_p, W^{m₁}_p)_{η,q} = B^{(1-η)m₀+ηm₁}_{p,q}` for `1 ≤ m₀ < m₁`
(`Rd.memKMethod_sobolevCouple_iff`).

By the interpolation property, an additive map bounded on `L_p` and on `W^m_p` is bounded on
`B^{θm}_{p,q}` (`Rd.kMethodNorm_map_le_of_bounded_lp_sobolev`,
`Rd.memApprox_map_of_bounded_lp_sobolev`).
-/

@[expose] public section

open MeasureTheory Module
open scoped ENNReal
open ENNReal (dyadicWeight)

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The grid norm of `W^m_p` -/

/-- The **grid norm of `W^m_p(V)`**: `‖f‖_p + inf ∑_α ‖g_α‖_p`, the infimum over all families
`(g_α)_α` in `L_p(V)`, indexed by the multi-indices `α = (α_0, …, α_{m-1})` with entries below
`n`, such that `g_α` is the weak derivative `∂_{e_{α_0}} ⋯ ∂_{e_{α_{m-1}}} f` along the basis `e`
of `Rd.gridBasis`.  It is finite exactly when all these weak derivatives exist in `L_p(V)`
(`Rd.exists_hasWeakLineDeriv_of_sobolevGridNorm_lt_top`, `Rd.sobolevGridNorm_le`). -/
noncomputable def sobolevGridNorm (m : ℕ) (f : Lp ℂ p (volume : Measure V)) : ℝ≥0∞ :=
  ‖f‖ₑ + ⨅ (g : (Fin m → Fin (finrank ℝ V)) → Lp ℂ p (volume : Measure V))
    (_ : ∀ i, HasWeakLineDeriv ⊤ (fun k => gridBasis V (i k)) f (g i)), ∑ i, ‖g i‖ₑ

/-- The grid norm is at most `‖f‖_p + ∑_α ‖g_α‖_p` for every family `(g_α)` of weak derivatives
of `f` of order `m` along the basis vectors. -/
theorem sobolevGridNorm_le {m : ℕ} {f : Lp ℂ p (volume : Measure V)}
    {g : (Fin m → Fin (finrank ℝ V)) → Lp ℂ p (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun k => gridBasis V (i k)) f (g i)) :
    sobolevGridNorm m f ≤ ‖f‖ₑ + ∑ i, ‖g i‖ₑ :=
  add_le_add_right (iInf₂_le g hg) _

/-- **The grid norm is `‖f‖_p + ∑_α ‖∂^{e_α} f‖_p`**: if `(g_α)` is a family of weak derivatives
of `f` of order `m` along the basis vectors, then the grid norm of `f` equals
`‖f‖_p + ∑_α ‖g_α‖_p`.  The infimum runs over one family only, since weak derivatives on `V` are
unique in `L_p(V)` (`Rd.HasWeakLineDeriv.eq_of_top`). -/
theorem sobolevGridNorm_eq {m : ℕ} {f : Lp ℂ p (volume : Measure V)}
    {g : (Fin m → Fin (finrank ℝ V)) → Lp ℂ p (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun k => gridBasis V (i k)) f (g i)) :
    sobolevGridNorm m f = ‖f‖ₑ + ∑ i, ‖g i‖ₑ :=
  le_antisymm (sobolevGridNorm_le hg) (add_le_add_right (le_iInf₂ fun g' hg' => by
    rw [funext fun i => (hg i).eq_of_top (hg' i)]) _)

/-- **A finite grid norm comes from weak derivatives**: if the grid norm of `f` is finite, then
`f` has weak derivatives `g_α ∈ L_p(V)` of order `m` along the basis vectors for every
multi-index `α`. -/
theorem exists_hasWeakLineDeriv_of_sobolevGridNorm_lt_top {m : ℕ}
    {f : Lp ℂ p (volume : Measure V)} (hf : sobolevGridNorm m f < ∞) :
    ∃ g : (Fin m → Fin (finrank ℝ V)) → Lp ℂ p (volume : Measure V),
      ∀ i, HasWeakLineDeriv ⊤ (fun k => gridBasis V (i k)) f (g i) := by
  obtain ⟨g, hg⟩ := iInf_lt_iff.1 (lt_of_le_of_lt le_add_self hf)
  exact ⟨g, (iInf_lt_iff.1 hg).choose⟩

/-- **Every `f ∈ W^m_p(V)` has finite grid norm**: the weak derivatives along the basis vectors
exist in `L_p(V)` (`Rd.memSobolev_iff_exists_hasWeakLineDeriv`). -/
theorem sobolevGridNorm_lt_top_of_memSobolev {m : ℕ} {f : Lp ℂ p (volume : Measure V)}
    (hf : MemSobolev m f) : sobolevGridNorm m f < ∞ := by
  have hd : ∀ i : Fin m → Fin (finrank ℝ V), ∃ g : Lp ℂ p (volume : Measure V),
      HasWeakLineDeriv ⊤ (fun k => gridBasis V (i k)) f g := fun i =>
    (memSobolev_iff_exists_hasWeakLineDeriv f).1 hf m le_rfl _
  choose g hg using hd
  exact (sobolevGridNorm_le hg).trans_lt
    (ENNReal.add_lt_top.2 ⟨eNorm_lt_top, ENNReal.sum_lt_top.2 fun _ _ => eNorm_lt_top⟩)

/-- **The grid norm is finite exactly on `W^m_p(V)`**: in dimension `n ≥ 1`, for `1 < p < ∞`,
`m ∈ ℕ` and `f ∈ L_p(V)`, the grid norm of `f` is finite iff `f ∈ W^m_p(V)`.  Weak derivatives
of order `m` along the basis vectors give `f ∈ F^m_{p,2}(V) = W^m_p(V)`
(`Rd.memTriebelLizorkin_of_hasWeakLineDeriv`, `Rd.memSobolev_iff_memTriebelLizorkin`). -/
theorem sobolevGridNorm_lt_top_iff [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    {f : Lp ℂ p (volume : Measure V)} : sobolevGridNorm m f < ∞ ↔ MemSobolev m f := by
  refine ⟨fun hf => ?_, sobolevGridNorm_lt_top_of_memSobolev⟩
  obtain ⟨g, hg⟩ := exists_hasWeakLineDeriv_of_sobolevGridNorm_lt_top hf
  exact (memSobolev_iff_memTriebelLizorkin hp1 hp f).2
    (memTriebelLizorkin_of_hasWeakLineDeriv hp1 hp hg)

/-! ### The grid norm between two Besov quasi-norms -/

variable (V p) in
/-- The constant `2 (1 - 2^{-m})⁻¹ (‖Φ‖_1 + 2^m ∑_α K_α)` of the bound of the Besov quasi-norm of
`B^m_{p,max(p,2)}` by the grid norm, with `K_α = Rd.sobolevToTLConst V p α`. -/
noncomputable def approxSobolevGridConst (m : ℕ) : ℝ≥0∞ :=
  2 * (1 - (2 : ℝ≥0∞) ^ (-(m : ℝ)))⁻¹ *
    (eLpNorm (lpKernel (V := V)) 1 volume + 2 ^ m * ∑ i : Fin m → Fin (finrank ℝ V),
      sobolevToTLConst V p i)

omit [Fact (1 ≤ p)] in
/-- The constant `Rd.approxSobolevGridConst V p m` is finite for `1 < p < ∞` and `m ≥ 1`. -/
theorem approxSobolevGridConst_ne_top (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ} (hm : 1 ≤ m) :
    approxSobolevGridConst V p m ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.two_mul_one_sub_two_rpow_neg_inv_ne_top (Nat.cast_pos.2 hm))
    (ENNReal.add_ne_top.2 ⟨eLpNorm_lpKernel_ne_top, ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
      (ENNReal.sum_ne_top.2 fun i _ => sobolevToTLConst_ne_top hp1 hp i)⟩)

omit [Fact (1 ≤ p)] in
/-- The constant `Rd.approxSobolevGridConst V p m` is nonzero, since `‖Φ‖_1 ≥ 1`
(`Rd.one_le_eLpNorm_lpKernel`). -/
theorem approxSobolevGridConst_ne_zero (m : ℕ) : approxSobolevGridConst V p m ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_
  · exact (zero_lt_one.trans_le (ENNReal.one_le_one_sub_two_rpow_neg_inv _)).ne'
  · exact (zero_lt_one.trans_le (one_le_eLpNorm_lpKernel.trans le_self_add)).ne'

/-- **The grid norm bounds `B^m_{p,max(p,2)}` for one family of derivatives**: under the
hypotheses of `Rd.approxNormDyadic_le_of_hasWeakLineDeriv`, the dyadic quasi-norm of `f` in
`A^m_{max(p,2)}` of the band-limited scheme is at most
`Rd.approxSobolevGridConst V p m · (‖f‖_p + ∑_α ‖g_α‖_p)`. -/
theorem approxNormDyadic_le_of_hasWeakLineDeriv_sum [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞)
    {m : ℕ} (hm : 1 ≤ m) {f : Lp ℂ p (volume : Measure V)}
    {g : (Fin m → Fin (finrank ℝ V)) → Lp ℂ p (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun k => gridBasis V (i k)) f (g i)) :
    (bandScheme hp).approxNormDyadic (m : ℝ) (max p 2) f ≤
      approxSobolevGridConst V p m * (‖f‖ₑ + ∑ i, ‖g i‖ₑ) := by
  have h : eLpNorm (lpKernel (V := V)) 1 volume * ‖f‖ₑ +
      2 ^ m * ∑ i, sobolevToTLConst V p i * ‖g i‖ₑ ≤
      (eLpNorm (lpKernel (V := V)) 1 volume +
        2 ^ m * ∑ i : Fin m → Fin (finrank ℝ V), sobolevToTLConst V p i) *
        (‖f‖ₑ + ∑ i, ‖g i‖ₑ) := by
    refine le_trans ?_ (ENNReal.mul_add_mul_le_add_mul_add _ _ _ _)
    rw [mul_assoc]
    exact add_le_add_right (mul_le_mul_right (ENNReal.sum_mul_le_sum_mul_sum _ _ _) _) _
  refine (approxNormDyadic_le_of_hasWeakLineDeriv hp1 hp hm hg).trans ?_
  rw [approxSobolevGridConst, mul_assoc _ (_ + _)]
  exact mul_le_mul_right h _

/-- **`W^m_p ⊆ B^m_{p,max(p,2)}` for the grid norm**: in dimension `n ≥ 1`, for `1 < p < ∞`,
`m ≥ 1` and `f ∈ L_p(V)`, the dyadic quasi-norm of `f` in `A^m_{max(p,2)}` of the band-limited
scheme is at most `Rd.approxSobolevGridConst V p m` times the grid norm of `f`. -/
theorem approxNormDyadic_le_sobolevGridNorm [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    (hm : 1 ≤ m) (f : Lp ℂ p (volume : Measure V)) :
    (bandScheme hp).approxNormDyadic (m : ℝ) (max p 2) f ≤
      approxSobolevGridConst V p m * sobolevGridNorm m f := by
  have hc0 := approxSobolevGridConst_ne_zero (V := V) (p := p) m
  have hc := approxSobolevGridConst_ne_top (V := V) hp1 hp hm
  rw [sobolevGridNorm, ENNReal.add_iInf₂, ENNReal.mul_iInf_of_ne hc0 hc]
  refine le_iInf fun g => ?_
  rw [ENNReal.mul_iInf_of_ne hc0 hc]
  exact le_iInf fun hg => approxNormDyadic_le_of_hasWeakLineDeriv_sum hp1 hp hm hg

variable (V p) in
/-- The constant `1 + (∑_α C_α) · 8 · 2^{3m} ‖Φ‖_1` of the bound of the grid norm by the Besov
quasi-norm of `B^m_{p,min(p,2)}`, with `C_α = Rd.tlToSobolevConst p (e_{α_0}, …, e_{α_{m-1}})`
for the basis `e` of `Rd.gridBasis`. -/
noncomputable def sobolevGridApproxConst (m : ℕ) : ℝ≥0∞ :=
  1 + (∑ i : Fin m → Fin (finrank ℝ V), tlToSobolevConst p (fun k => gridBasis V (i k))) *
    (8 * dyadicWeight (m : ℝ) 3 * eLpNorm (lpKernel (V := V)) 1 volume)

omit [Fact (1 ≤ p)] in
/-- The constant `Rd.sobolevGridApproxConst V p m` is finite for `1 < p < ∞`. -/
theorem sobolevGridApproxConst_ne_top (hp1 : 1 < p) (hp : p ≠ ∞) (m : ℕ) :
    sobolevGridApproxConst V p m ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top
    (ENNReal.sum_ne_top.2 fun _ _ => tlToSobolevConst_ne_top hp1 hp _)
    (eight_mul_dyadicWeight_mul_eLpNorm_lpKernel_ne_top _)⟩

omit [Fact (1 ≤ p)] in
/-- The constant `Rd.sobolevGridApproxConst V p m` is nonzero: it is at least `1`. -/
theorem sobolevGridApproxConst_ne_zero (m : ℕ) : sobolevGridApproxConst V p m ≠ 0 :=
  (zero_lt_one.trans_le (le_self_add : (1 : ℝ≥0∞) ≤ 1 + _)).ne'

/-- **`B^m_{p,min(p,2)} ⊆ W^m_p` for the grid norm**: in dimension `n ≥ 1`, for `1 < p < ∞`,
`m ∈ ℕ` and `f ∈ L_p(V)`, the grid norm of `f` is at most `Rd.sobolevGridApproxConst V p m` times
the dyadic quasi-norm of `f` in `A^m_{min(p,2)}` of the band-limited scheme
(`Rd.exists_hasWeakLineDeriv_of_memApprox` for every multi-index). -/
theorem sobolevGridNorm_le_approxNormDyadic [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) (m : ℕ)
    (f : Lp ℂ p (volume : Measure V)) :
    sobolevGridNorm m f ≤
      sobolevGridApproxConst V p m * (bandScheme hp).approxNormDyadic (m : ℝ) (min p 2) f := by
  by_cases hf : (bandScheme hp).MemApprox (m : ℝ) (min p 2) f
  · have hd := fun i : Fin m → Fin (finrank ℝ V) =>
      exists_hasWeakLineDeriv_of_memApprox hp1 hp le_rfl (fun k => gridBasis V (i k)) hf
    choose g hg hgn using hd
    refine (sobolevGridNorm_le hg).trans ?_
    rw [sobolevGridApproxConst, add_mul, one_mul, mul_assoc, Finset.sum_mul]
    gcongr with i
    · exact (bandScheme hp).enorm_le_approxNormDyadic f
    · exact hgn i
  · have hN : (bandScheme hp).approxNormDyadic (m : ℝ) (min p 2) f = ∞ := by
      by_contra h
      exact hf ((ApproximationScheme.memApprox_iff_approxNormDyadic_lt_top
        (le_min Fact.out one_le_two) (Nat.cast_nonneg m)).2 (lt_top_iff_ne_top.2 h))
    rw [hN, ENNReal.mul_top (sobolevGridApproxConst_ne_zero m)]
    exact le_top

/-! ### Real interpolation -/

/-- The **couple `(L_p, W^m_p)`** on `L_p(V)`: the `L_p` norm and the grid norm of `W^m_p(V)`
(`Rd.sobolevGridNorm`). -/
noncomputable def lpSobolevCouple (m : ℕ) : InterpCouple (Lp ℂ p (volume : Measure V)) :=
  ⟨fun f => ‖f‖ₑ, sobolevGridNorm m⟩

/-- The first norm of `(L_p, W^m_p)` is the `L_p` norm. -/
@[simp]
theorem lpSobolevCouple_norm0 {m : ℕ} (f : Lp ℂ p (volume : Measure V)) :
    (lpSobolevCouple m).norm0 f = ‖f‖ₑ := rfl

/-- The second norm of `(L_p, W^m_p)` is the grid norm of `W^m_p`. -/
@[simp]
theorem lpSobolevCouple_norm1 {m : ℕ} (f : Lp ℂ p (volume : Measure V)) :
    (lpSobolevCouple m).norm1 f = sobolevGridNorm m f := rfl

/-- The **couple `(W^{m₀}_p, W^{m₁}_p)`** on `L_p(V)`: the grid norms of `W^{m₀}_p(V)` and
`W^{m₁}_p(V)`. -/
noncomputable def sobolevCouple (m₀ m₁ : ℕ) : InterpCouple (Lp ℂ p (volume : Measure V)) :=
  ⟨sobolevGridNorm m₀, sobolevGridNorm m₁⟩

/-- The first norm of `(W^{m₀}_p, W^{m₁}_p)` is the grid norm of `W^{m₀}_p`. -/
@[simp]
theorem sobolevCouple_norm0 {m₀ m₁ : ℕ} (f : Lp ℂ p (volume : Measure V)) :
    (sobolevCouple m₀ m₁).norm0 f = sobolevGridNorm m₀ f := rfl

/-- The second norm of `(W^{m₀}_p, W^{m₁}_p)` is the grid norm of `W^{m₁}_p`. -/
@[simp]
theorem sobolevCouple_norm1 {m₀ m₁ : ℕ} (f : Lp ℂ p (volume : Measure V)) :
    (sobolevCouple m₀ m₁).norm1 f = sobolevGridNorm m₁ f := rfl

variable {θ η : ℝ} {q : ℝ≥0∞}

/-- **`(L_p, W^m_p)_{θ,q} = B^{θm}_{p,q}`** (Bergh–Löfström, Theorem 6.4.5(4) with
`H^m_p = W^m_p` from Theorem 6.2.3): in dimension
`n ≥ 1`, for `1 < p < ∞`, `m ≥ 1`, `0 < θ < 1` and `1 ≤ q ≤ ∞`, `f ∈ L_p(V)` lies in the real
interpolation space of the couple `(L_p, W^m_p)` iff `f` lies in the approximation space
`A^{θm}_q` of the band-limited scheme, the Besov space `B^{θm}_{p,q}(V)`.  The grid norm lies
between the quasi-norms of `B^m_{p,min(p,2)}` and `B^m_{p,max(p,2)}`
(`ApproximationScheme.memKMethod_iff_memApprox_of_sandwich`). -/
theorem memKMethod_lpSobolevCouple_iff [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    (hm : 1 ≤ m) (hθ : 0 < θ) (hθ' : θ < 1) (hq : 1 ≤ q) {f : Lp ℂ p (volume : Measure V)} :
    (lpSobolevCouple m).MemKMethod θ q f ↔ (bandScheme hp).MemApprox (θ * m) q f :=
  ApproximationScheme.memKMethod_iff_memApprox_of_sandwich (N₁ := sobolevGridNorm m)
    (sobolevGridApproxConst_ne_top hp1 hp m) (approxSobolevGridConst_ne_top hp1 hp hm)
    (le_min Fact.out one_le_two) (le_max_of_le_right one_le_two) (Nat.cast_pos.2 hm) hθ hθ' hq
    (sobolevGridNorm_le_approxNormDyadic hp1 hp m) (approxNormDyadic_le_sobolevGridNorm hp1 hp hm)

/-- **`(W^{m₀}_p, W^{m₁}_p)_{η,q} = B^{(1-η)m₀+ηm₁}_{p,q}`** (Bergh–Löfström,
Theorem 6.4.5(4) with `H^m_p = W^m_p` from Theorem 6.2.3): in dimension `n ≥ 1`, for
`1 < p < ∞`, orders `1 ≤ m₀ < m₁`, `0 < η < 1` and `1 ≤ q ≤ ∞`, `f ∈ L_p(V)` lies in the real
interpolation space of the couple `(W^{m₀}_p, W^{m₁}_p)` iff `f` lies in the Besov space
`B^{(1-η)m₀+ηm₁}_{p,q}(V)`, the approximation space of the band-limited scheme
(`ApproximationScheme.memKMethod_iff_memApprox_of_two_sandwiches`). -/
theorem memKMethod_sobolevCouple_iff [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {m₀ m₁ : ℕ}
    (hm₀ : 1 ≤ m₀) (hm : m₀ < m₁) (hη : 0 < η) (hη' : η < 1) (hq : 1 ≤ q)
    {f : Lp ℂ p (volume : Measure V)} :
    (sobolevCouple m₀ m₁).MemKMethod η q f ↔
      (bandScheme hp).MemApprox ((1 - η) * m₀ + η * m₁) q f :=
  ApproximationScheme.memKMethod_iff_memApprox_of_two_sandwiches (N₀ := sobolevGridNorm m₀)
    (N₁ := sobolevGridNorm m₁) (sobolevGridApproxConst_ne_top hp1 hp m₀)
    (approxSobolevGridConst_ne_top hp1 hp hm₀) (sobolevGridApproxConst_ne_top hp1 hp m₁)
    (approxSobolevGridConst_ne_top hp1 hp (hm₀.trans hm.le)) (le_min Fact.out one_le_two)
    (le_max_of_le_right one_le_two) (le_min Fact.out one_le_two) (le_max_of_le_right one_le_two)
    (Nat.cast_pos.2 hm₀) (Nat.cast_lt.2 hm) hη hη' hq
    (sobolevGridNorm_le_approxNormDyadic hp1 hp m₀) (approxNormDyadic_le_sobolevGridNorm hp1 hp hm₀)
    (sobolevGridNorm_le_approxNormDyadic hp1 hp m₁)
    (approxNormDyadic_le_sobolevGridNorm hp1 hp (hm₀.trans hm.le))

/-! ### Operators bounded on `L_p` and on `W^m_p` -/

/-- **An operator bounded on `L_p` and on `W^m_p` is bounded in the K-norm**. This applies
`InterpCouple.kMethodNorm_map_le` in its full parameter range, extending the classical
exactness estimate of Bergh–Löfström, Theorem 3.1.2.
If `T : L_p(V) → L_p(V)` is additive with `‖T f‖_p ≤ M₀ ‖f‖_p`
and `‖T f‖_{W^m_p} ≤ M₁ ‖f‖_{W^m_p}` in the grid norm for every `f`, and `0 < M₀, M₁ < ∞`, then
`‖T f‖_{K,θ,q} ≤ M₀^(1-θ) M₁^θ ‖f‖_{K,θ,q}` in the K-norm of `(L_p, W^m_p)`, whose space is
`B^{θm}_{p,q}` for `n ≥ 1`, `1 < p < ∞`, `m ≥ 1`, `0 < θ < 1` and `1 ≤ q ≤ ∞`
(`Rd.memKMethod_lpSobolevCouple_iff`). -/
theorem kMethodNorm_map_le_of_bounded_lp_sobolev {m : ℕ}
    (T : Lp ℂ p (volume : Measure V) →+ Lp ℂ p (volume : Measure V)) {M₀ M₁ : ℝ≥0∞}
    (hM₀ : M₀ ≠ 0) (hM₀' : M₀ ≠ ∞) (hM₁ : M₁ ≠ 0) (hM₁' : M₁ ≠ ∞)
    (h₀ : ∀ f, ‖T f‖ₑ ≤ M₀ * ‖f‖ₑ) (h₁ : ∀ f, sobolevGridNorm m (T f) ≤ M₁ * sobolevGridNorm m f)
    (f : Lp ℂ p (volume : Measure V)) :
    (lpSobolevCouple m).kMethodNorm θ q (T f) ≤
      M₀ ^ (1 - θ) * M₁ ^ θ * (lpSobolevCouple m).kMethodNorm θ q f :=
  InterpCouple.kMethodNorm_map_le T hM₀ hM₀' hM₁ hM₁' h₀ h₁ f

/-- **An operator bounded on `L_p` and on `W^m_p` maps `B^{θm}_{p,q}` into itself**: in dimension
`n ≥ 1`, for `1 < p < ∞`, `m ≥ 1`, `0 < θ < 1` and `1 ≤ q ≤ ∞`, if `T : L_p(V) → L_p(V)` is
additive with `‖T f‖_p ≤ M₀ ‖f‖_p` and `‖T f‖_{W^m_p} ≤ M₁ ‖f‖_{W^m_p}` in the grid norm with
finite `M₀, M₁`, then `T f ∈ B^{θm}_{p,q}(V)` for every `f ∈ B^{θm}_{p,q}(V)`
(`InterpCouple.MemKMethod.map`, `Rd.memKMethod_lpSobolevCouple_iff`). -/
theorem memApprox_map_of_bounded_lp_sobolev [Nontrivial V] (hp1 : 1 < p) (hp : p ≠ ∞) {m : ℕ}
    (hm : 1 ≤ m) (hθ : 0 < θ) (hθ' : θ < 1) (hq : 1 ≤ q)
    (T : Lp ℂ p (volume : Measure V) →+ Lp ℂ p (volume : Measure V)) {M₀ M₁ : ℝ≥0∞}
    (hM₀ : M₀ ≠ ∞) (hM₁ : M₁ ≠ ∞) (h₀ : ∀ f, ‖T f‖ₑ ≤ M₀ * ‖f‖ₑ)
    (h₁ : ∀ f, sobolevGridNorm m (T f) ≤ M₁ * sobolevGridNorm m f)
    {f : Lp ℂ p (volume : Measure V)} (hf : (bandScheme hp).MemApprox (θ * m) q f) :
    (bandScheme hp).MemApprox (θ * m) q (T f) :=
  (memKMethod_lpSobolevCouple_iff hp1 hp hm hθ hθ' hq).1
    (InterpCouple.MemKMethod.map (A := lpSobolevCouple m) (B := lpSobolevCouple m) T hM₀ hM₁ h₀ h₁
      ((memKMethod_lpSobolevCouple_iff hp1 hp hm hθ hθ' hq).2 hf))

end Rd
