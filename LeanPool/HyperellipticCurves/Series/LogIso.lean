/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.ForMathlib.LocalRing
public import LeanPool.HyperellipticCurves.Series.FormalGroupLaw

/-!
# The logarithm as a homomorphism

The formal logarithm `Λ` of a formal group law is a homomorphism on `𝔪ⁿ`, for `𝔪 = (π)`
the maximal ideal of a local ring of residue characteristic `p` and absolute ramification
index at most `e < p - 1`: the `π`-scaled log `HL` (with
`f(coeff_d HL) = f(π)^{deg d}·coeff_d Λ`) turns the `π`-scaled formal group sum
`ChabautyColeman.FormalGroupLaw.scaledF` — `F(πX, πY)/π`, integral with decaying
coefficients, so convergent on all of `Oⁿ × Oⁿ` — into addition
(`ChabautyColeman.FormalGroupLaw.log_addHom`); `Λ(π·y) = f(evalT y (HL i))`.

Additivity descends the `K`-power-series identity `Λ(F(X,Y)) = Λ(X) + Λ(Y)` (`log_subst_F`)
to the `π`-scaled integral forms — via `rescale`/`subst_comp_subst_apply`/`map_subst` and
`f` injective (`subst_scaledF_descent`) — and then evaluates it with `evalT_subst`. The
scaled log is uniquely determined by its scaling relation
(`ChabautyColeman.FormalGroupLaw.scaled_log_unique`).

The canonical form consumed downstream (`LeanPool.HyperellipticCurves.Log.Analytic.Lam`,
`LeanPool.HyperellipticCurves.Log.Analytic.ColemanIntegral`) is
`ChabautyColeman.FormalGroupLaw.scaledLog`,
with its API `coeff_scaledLog_map`, `decay_scaledLog`, `evalT_scaledLog_add`.

(`Λ` is moreover *injective* on `(pO)ⁿ` in the unramified case, via the formal exponential; this is
formalized in `upstream HyperellipticCurves.Archive.LogInjective`, and the main theorems do not use
it.)

Blueprint node: `thm:log-iso`.
-/

@[expose] public section

open MvPowerSeries IsLocalRing Filter Topology ChabautyColeman.MvPSeries

namespace ChabautyColeman.FormalGroupLaw

section Helpers

variable {O : Type*} [CommRing O] {ι : Type*} {K : Type*} [CommRing K]
  {f : O →+* K} {c : O}

theorem map_eq_rescale {H : MvPowerSeries ι O} {L : MvPowerSeries ι K}
    (hH : ∀ d, f (coeff d H) = f c ^ d.degree * coeff d L) :
    MvPowerSeries.map f H = rescale (fun _ ↦ f c) L := by
  ext d
  rw [coeff_map, hH d, coeff_rescale]
  congr 1
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply]

theorem map_injective_of_injective (hf : Function.Injective f) :
    Function.Injective (MvPowerSeries.map (σ := ι) f) := fun φ ψ h ↦ by
  ext d; exact hf (by rw [← coeff_map, ← coeff_map, h])

theorem rescale_const_eq_subst (a : K) (L : MvPowerSeries ι K) :
    rescale (fun _ ↦ a) L = subst (fun j ↦ a • X j) L := by
  rw [rescale_eq_subst]; rfl

end Helpers

/-! ### The scaled formal group law -/

section ScaledF

variable {O : Type*} [CommRing O] {ι : Type*} (Φ : FormalGroupLaw O ι) (c : O)

/-- The `c`-scaled formal group law: `F(cX, cY)/c`, integral because `F` has no constant
term. For `c` in the maximal ideal its coefficients decay, so it evaluates on all of
`Oⁿ × Oⁿ`. -/
noncomputable def scaledF (j : ι) : MvPowerSeries (ι ⊕ ι) O :=
  fun d ↦ c ^ (d.degree - 1) * coeff d (Φ.F j)

@[simp]
theorem coeff_scaledF (j : ι) (d : ι ⊕ ι →₀ ℕ) :
    coeff d (Φ.scaledF c j) = c ^ (d.degree - 1) * coeff d (Φ.F j) := rfl

theorem constantCoeff_scaledF (j : ι) : constantCoeff (Φ.scaledF c j) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_scaledF, map_zero Finsupp.degree,
    coeff_zero_eq_constantCoeff_apply, Φ.zero_constantCoeff, mul_zero]

variable [Finite ι] in
theorem hasSubst_scaledF : MvPowerSeries.HasSubst (Φ.scaledF c) :=
  hasSubst_of_constantCoeff_zero fun j ↦ Φ.constantCoeff_scaledF c j

end ScaledF

section ScaledFTop

variable {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] {ι : Type*} [Finite ι]
  (Φ : FormalGroupLaw O ι) {c : O}

/-- The coefficients of the scaled group law tend to zero, for a scaling factor in the
maximal ideal. -/
theorem decay_scaledF (hc : c ∈ maximalIdeal O) (j : ι) :
    Tendsto (fun d ↦ coeff d (Φ.scaledF c j)) cofinite (𝓝 0) := by
  refine MvPSeries.tendsto_coeff_zero_of_mem_pow
    (fun d ↦ Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hc _)) ?_
  exact (tendsto_sub_atTop_nat 1).comp Finsupp.tendsto_degree_cofinite

end ScaledFTop

section ScaledFEval

variable {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] {ι : Type*} [Finite ι] {c : O} (Φ : FormalGroupLaw O ι)

/-! ### Evaluation of the scaled group law at scaled points -/

/-- Evaluating the `c`-scaled group law and rescaling recovers the group law at the
`c`-scaled point: `c · (F(cy, cz)/c) = F(cy, cz)` at the level of `evalT`. -/
theorem mul_evalT_scaledF (hc : c ∈ maximalIdeal O) (y : ι ⊕ ι → O) (j : ι) :
    c * evalT y (Φ.scaledF c j) = evalT (fun s ↦ c * y s) (Φ.F j) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  rw [evalT_eq_tsum, evalT_eq_tsum,
    ← (MvPSeries.summable_evalT y (Φ.decay_scaledF hc j)).tsum_mul_left]
  refine tsum_congr fun d ↦ ?_
  rw [coeff_scaledF]
  rcases Nat.eq_zero_or_pos d.degree with h0 | hpos
  · obtain rfl : d = 0 := (Finsupp.degree_eq_zero_iff d).mp h0
    simp [coeff_zero_eq_constantCoeff_apply, Φ.zero_constantCoeff j]
  · have hprod : (d.prod fun s k ↦ (c * y s) ^ k)
        = c ^ d.degree * d.prod fun s k ↦ y s ^ k := by
      rw [Finsupp.prod, Finsupp.prod,
        show (∏ s ∈ d.support, (c * y s) ^ d s) = ∏ s ∈ d.support, c ^ d s * y s ^ d s from
          Finset.prod_congr rfl fun s _ ↦ mul_pow _ _ _,
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply]
    have hpp : c * c ^ (d.degree - 1) = c ^ d.degree := by
      rw [← pow_succ', Nat.sub_add_cancel hpos]
    rw [hprod, ← hpp]
    ring

end ScaledFEval

section Descent

variable {O : Type*} [CommRing O] {ι : Type*} [Finite ι] {K : Type*} [CommRing K]
  {f : O →+* K} {c : O} (Φ : FormalGroupLaw O ι)

private lemma subst_smulX_subst_X_comp {a : K} (emb : ι → ι ⊕ ι) (L : MvPowerSeries ι K) :
    MvPowerSeries.subst (fun t : ι ⊕ ι ↦ a • (X t : MvPowerSeries (ι ⊕ ι) K))
        (MvPowerSeries.subst (fun s : ι ↦ (X (emb s) : MvPowerSeries (ι ⊕ ι) K)) L)
      = MvPowerSeries.subst
          (fun s : ι ↦ a • (X (emb s) : MvPowerSeries (ι ⊕ ι) K)) L := by
  have he : HasSubst fun s : ι ↦ (X (emb s) : MvPowerSeries (ι ⊕ ι) K) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have hpX2 : HasSubst fun t : ι ⊕ ι ↦ a • (X t : MvPowerSeries (ι ⊕ ι) K) :=
    HasSubst.smul_X _
  rw [subst_comp_subst_apply he hpX2]
  congr 1
  funext s
  exact subst_X hpX2 _

private lemma map_subst_X_comp {a : K} (emb : ι → ι ⊕ ι) {H : MvPowerSeries ι O}
    {L : MvPowerSeries ι K} (hH : MvPowerSeries.map f H = rescale (fun _ ↦ a) L) :
    MvPowerSeries.map f
        (MvPowerSeries.subst (fun s : ι ↦ (X (emb s) : MvPowerSeries (ι ⊕ ι) O)) H)
      = MvPowerSeries.subst
          (fun s : ι ↦ a • (X (emb s) : MvPowerSeries (ι ⊕ ι) K)) L := by
  have heO : HasSubst fun s : ι ↦ (X (emb s) : MvPowerSeries (ι ⊕ ι) O) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have heK : HasSubst fun s : ι ↦ (X (emb s) : MvPowerSeries (ι ⊕ ι) K) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by simp
  have hpX : HasSubst fun j : ι ↦ a • (X j : MvPowerSeries ι K) :=
    HasSubst.smul_X _
  have hXe : (fun s : ι ↦ MvPowerSeries.map f (X (emb s) : MvPowerSeries (ι ⊕ ι) O))
      = fun s : ι ↦ (X (emb s) : MvPowerSeries (ι ⊕ ι) K) :=
    funext fun s ↦ MvPowerSeries.map_X f (emb s)
  rw [map_subst heO, hXe, hH, rescale_const_eq_subst, subst_comp_subst_apply hpX heK]
  congr 1
  funext s
  rw [subst_smul heK, subst_X heK]

/-- The `c`-scaled formal group law is the `f c`-rescaling of `F`, over the fraction
field. -/
theorem map_scaledF_smul (j : ι) :
    f c • MvPowerSeries.map f (Φ.scaledF c j)
      = rescale (fun _ ↦ f c) ((Φ.map f).F j) := by
  ext d
  rw [MvPowerSeries.coeff_smul, coeff_map, coeff_scaledF, coeff_rescale, map_mul, map_pow,
    Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply]
  rcases Nat.eq_zero_or_pos d.degree with h0 | hpos
  · obtain rfl : d = 0 := (Finsupp.degree_eq_zero_iff d).mp h0
    simp [coeff_zero_eq_constantCoeff_apply, Φ.zero_constantCoeff j]
  · rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hpos, F_map, coeff_map]

end Descent

section DescentLog

variable {O : Type*} [CommRing O] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {K : Type*} [Field K] {f : O →+* K} {c : O} (Φ : FormalGroupLaw O ι)

/-- The `c`-scaled logarithms over `O` are uniquely determined by their scaling relation
(the base-change map `f` is injective), so any two packages producing such series — e.g.
`ChabautyColeman.FormalGroupLaw.log_addHom` and the canonical
`ChabautyColeman.FormalGroupLaw.scaledLog` — contain the same series. -/
theorem scaled_log_unique (hf : Function.Injective f) {HL HL' : ι → MvPowerSeries ι O}
    (h : ∀ i d, f (coeff d (HL i)) = f c ^ d.degree * coeff d ((Φ.map f).log i))
    (h' : ∀ i d, f (coeff d (HL' i)) = f c ^ d.degree * coeff d ((Φ.map f).log i)) :
    HL = HL' :=
  funext fun i ↦ MvPowerSeries.ext fun d ↦ hf ((h i d).trans (h' i d).symm)

variable [CharZero K]

/-- The descended additivity identity: the `c`-scaled logarithm is additive for the
`c`-scaled formal group law, over `O`. -/
theorem subst_scaledF_descent (hf : Function.Injective f) {HL : ι → MvPowerSeries ι O}
    (hHL : ∀ j, MvPowerSeries.map f (HL j)
      = rescale (fun _ ↦ f c) ((Φ.map f).log j)) (i : ι) :
    MvPowerSeries.subst (Φ.scaledF c) (HL i)
      = MvPowerSeries.subst
          (fun s : ι ↦ (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) O)) (HL i)
        + MvPowerSeries.subst
            (fun s : ι ↦ (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) O)) (HL i) := by
  have hpX : HasSubst (fun j : ι ↦ f c • (X j : MvPowerSeries ι K)) :=
    HasSubst.smul_X _
  have hpX2 : HasSubst (fun t : ι ⊕ ι ↦ f c • (X t : MvPowerSeries (ι ⊕ ι) K)) :=
    HasSubst.smul_X _
  have hmsF : HasSubst fun j ↦ MvPowerSeries.map f (Φ.scaledF c j) :=
    hasSubst_of_constantCoeff_zero fun s ↦ by rw [constantCoeff_map, Φ.constantCoeff_scaledF,
      map_zero]
  apply map_injective_of_injective hf
  rw [map_add, map_subst_X_comp Sum.inl (hHL i), map_subst_X_comp Sum.inr (hHL i)]
  calc MvPowerSeries.map f (MvPowerSeries.subst (Φ.scaledF c) (HL i))
      = MvPowerSeries.subst (fun j ↦ MvPowerSeries.map f (Φ.scaledF c j))
          (MvPowerSeries.map f (HL i)) := map_subst (Φ.hasSubst_scaledF c) (HL i)
    _ = MvPowerSeries.subst (fun j ↦ MvPowerSeries.map f (Φ.scaledF c j))
          (MvPowerSeries.subst (fun j ↦ f c • X j) ((Φ.map f).log i)) := by
        rw [hHL, rescale_const_eq_subst]
    _ = MvPowerSeries.subst (fun j ↦ f c • MvPowerSeries.map f (Φ.scaledF c j))
          ((Φ.map f).log i) := by
        rw [subst_comp_subst_apply hpX hmsF]
        congr 1
        funext j
        rw [subst_smul hmsF, subst_X hmsF]
    _ = MvPowerSeries.subst
          (fun j ↦ MvPowerSeries.subst (fun t : ι ⊕ ι ↦ f c • X t) ((Φ.map f).F j))
          ((Φ.map f).log i) := by
        congr 1
        funext j
        rw [Φ.map_scaledF_smul j, rescale_const_eq_subst]
    _ = MvPowerSeries.subst (fun t : ι ⊕ ι ↦ f c • X t)
          (MvPowerSeries.subst (fun j ↦ (Φ.map f).F j) ((Φ.map f).log i)) :=
        (subst_comp_subst_apply (Φ.map f).hasSubst_F hpX2 _).symm
    _ = MvPowerSeries.subst
          (fun s : ι ↦ f c • (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) K))
          ((Φ.map f).log i)
        + MvPowerSeries.subst
            (fun s : ι ↦ f c • (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) K))
            ((Φ.map f).log i) := by
        rw [(Φ.map f).log_subst_F i, ← coe_substAlgHom hpX2, map_add, coe_substAlgHom hpX2,
          subst_smulX_subst_X_comp Sum.inl, subst_smulX_subst_X_comp Sum.inr]

end DescentLog

/-! ### The homomorphism property of the logarithm -/

section AddHom

variable {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {K : Type*} [Field K] [CharZero K] {f : O →+* K} {π : O} {p e : ℕ}

open MvPSeries in
/-- **The formal logarithm is a homomorphism** on `𝔪ⁿ`, for a uniformizer `π` of a local ring of
residue characteristic `p` and absolute ramification index at most `e < p - 1`: the `π`-scaled log
`HL` turns the (everywhere-convergent) `π`-scaled formal group sum into addition. (Its injectivity
on `(pO)ⁿ` in the unramified case is formalized in `upstream
HyperellipticCurves.Archive.LogInjective`.)
-/ theorem log_addHom (hram : IsUniformizer π p e) (hpe : e + 1 < p) (hf : Function.Injective f)
    (Φ : FormalGroupLaw O ι) :
    ∃ HL : ι → MvPowerSeries ι O,
      (∀ i d, f (coeff d (HL i)) = f π ^ d.degree * coeff d ((Φ.map f).log i)) ∧
      ∀ (y z : ι → O) (i : ι),
        evalT (fun j ↦ evalT (Sum.elim y z) (Φ.scaledF π j)) (HL i)
          = evalT y (HL i) + evalT z (HL i) := by
  have hfp : f (p : O) ≠ 0 := by rw [map_natCast]; exact_mod_cast hram.prime.pos.ne'
  choose HL hHL_scale hHL_decay using fun i ↦ Φ.exists_integral_scaled_log hram hpe f hfp i
  refine ⟨HL, hHL_scale, fun y z i ↦ ?_⟩
  have hdX {emb : ι → ι ⊕ ι} (he : Function.Injective emb) : Tendsto (fun d ↦ coeff d
      (MvPowerSeries.subst (fun s : ι ↦ (X (emb s) : MvPowerSeries (ι ⊕ ι) O)) (HL i)))
      cofinite (𝓝 0) := by
    have h1 : (fun s : ι ↦ (X (emb s) : MvPowerSeries (ι ⊕ ι) O)) = X ∘ emb := rfl
    rw [h1, ← rename_eq_subst]
    exact decay_rename he (hHL_decay i)
  rw [← evalT_subst (Sum.elim y z) (Φ.hasSubst_scaledF π) (hHL_decay i)
      (Φ.decay_scaledF hram.mem),
    Φ.subst_scaledF_descent hf (fun j ↦ map_eq_rescale (hHL_scale j)) i,
    evalT_add _ (hdX Sum.inl_injective) (hdX Sum.inr_injective),
    evalT_subst (Sum.elim y z) hasSubst_Xemb (hHL_decay i) fun s ↦ decay_X _,
    evalT_subst (Sum.elim y z) hasSubst_Yemb (hHL_decay i) fun s ↦ decay_X _]
  have hyl : (fun s ↦ MvPSeries.evalT (Sum.elim y z)
      (X (Sum.inl s) : MvPowerSeries (ι ⊕ ι) O)) = y :=
    funext fun s ↦ by rw [evalT_X, Sum.elim_inl]
  have hzr : (fun s ↦ MvPSeries.evalT (Sum.elim y z)
      (X (Sum.inr s) : MvPowerSeries (ι ⊕ ι) O)) = z :=
    funext fun s ↦ by rw [evalT_X, Sum.elim_inr]
  rw [hyl, hzr]

end AddHom

/-! ### The canonical scaled logarithm -/

section ScaledLogDef

variable {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {K : Type*} [Field K] {f : O →+* K} {π : O} {p e : ℕ} (Φ : FormalGroupLaw O ι)

/-- The `π`-scaled logarithm of a formal group law, as a power series over `O`: the
integral form of `Λ(πU)`, so that `y ↦ evalT y (scaledLog i)` represents `Λ(π·y)`. -/
noncomputable def scaledLog (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    (f : O →+* K) (hfp : f (p : O) ≠ 0) (i : ι) : MvPowerSeries ι O :=
  (Φ.exists_integral_scaled_log hram hpe f hfp i).choose

theorem coeff_scaledLog_map (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    (hfp : f (p : O) ≠ 0) (i : ι) (d : ι →₀ ℕ) :
    f (coeff d (Φ.scaledLog hram hpe f hfp i))
      = f π ^ d.degree * coeff d ((Φ.map f).log i) :=
  (Φ.exists_integral_scaled_log hram hpe f hfp i).choose_spec.1 d

theorem decay_scaledLog (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    (hfp : f (p : O) ≠ 0) (i : ι) :
    Tendsto (fun d ↦ coeff d (Φ.scaledLog hram hpe f hfp i)) cofinite (𝓝 0) :=
  (Φ.exists_integral_scaled_log hram hpe f hfp i).choose_spec.2

end ScaledLogDef

section ScaledLogEval

variable {O : Type*} [CommRing O] [IsLocalRing O] [UniformSpace O]
  [Fact (IsAdic (maximalIdeal O))] [IsUniformAddGroup O] [CompleteSpace O] [T2Space O]
  [IsTopologicalRing O] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {K : Type*} [Field K] [CharZero K] {f : O →+* K} {π : O} {p e : ℕ}
  (Φ : FormalGroupLaw O ι)

/-- **Additivity of the formal logarithm**, for the canonical scaled log. -/
theorem evalT_scaledLog_add (hram : IsUniformizer π p e) (hpe : e + 1 < p)
    (hf : Function.Injective f) (hfp : f (p : O) ≠ 0) (y z : ι → O) (i : ι) :
    evalT (fun j ↦ evalT (Sum.elim y z) (Φ.scaledF π j)) (Φ.scaledLog hram hpe f hfp i)
      = evalT y (Φ.scaledLog hram hpe f hfp i) + evalT z (Φ.scaledLog hram hpe f hfp i) := by
  obtain ⟨HL, hsc, hadd⟩ := Φ.log_addHom hram hpe hf
  have hEq : Φ.scaledLog hram hpe f hfp = HL :=
    Φ.scaled_log_unique hf (fun i d ↦ Φ.coeff_scaledLog_map hram hpe hfp i d) hsc
  rw [hEq]
  exact hadd y z i

end ScaledLogEval

end ChabautyColeman.FormalGroupLaw

end
