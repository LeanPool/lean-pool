/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicGermWeierstrassPreparation
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.RegularLocusDense

/-!
# The tower of germ rings `𝒪_k ⊆ 𝒪_n` and Weierstrass polynomials in a coordinate

For `k ≤ n` the projection `ℂⁿ → ℂᵏ` onto the first `k` coordinates induces the inclusion
`𝒪_k → 𝒪_n` (`HolGerm.projGerm`).  A Weierstrass polynomial in the coordinate `z_k`
(`k < n`, `0`-indexed) over `𝒪_k` is the germ
`z_k ^ s + ∑_{j<s} A_j(z_0, …, z_{k-1}) z_k ^ j` with `A_j(0) = 0`
(`HolGerm.weierstrassGerm`).  On a product `E × ℂ` the analogous germ in the last variable
is `HolGerm.prodWeierstrassGerm`.

This file collects the transport lemmas between these rings, and the germ-level
forms of Weierstrass preparation and division:

* `HolGerm.exists_mul_comapEquiv_eq_prodWeierstrassGerm`: after a linear change of
  coordinates, a unit multiple of a nonzero germ on `E × ℂ` is a Weierstrass polynomial;
* `HolGerm.exists_eq_mul_prodWeierstrassGerm_add`: division by a Weierstrass polynomial on
  `E × ℂ`;
* `HolGerm.exists_eq_mul_weierstrassGerm_add`: the same on `ℂ^{n+1}` in the last coordinate.
-/

@[expose] public section

open Filter Topology

namespace SGPT.Foundations.Analysis.Pending

open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open HolomorphicGermWeierstrassPreparation

noncomputable section

namespace HolGerm

section General

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

theorem comap_comap (L : E →L[ℂ] F) (M : F →L[ℂ] G) (g : HolGerm G) :
    comap L (comap M g) = comap (M.comp L) g := by
  induction g using induction_on with
  | h f hf => rfl

theorem comap_id (g : HolGerm E) : comap (ContinuousLinearMap.id ℂ E) g = g := by
  induction g using induction_on with
  | h f hf => rfl

theorem comapEquiv_apply (L : E ≃L[ℂ] F) (g : HolGerm F) :
    comapEquiv L g = comap (L : E →L[ℂ] F) g :=
  rfl

theorem comapEquiv_trans_apply (L₁ : E ≃L[ℂ] F) (L₂ : F ≃L[ℂ] G) (g : HolGerm G) :
    comapEquiv (L₁.trans L₂) g = comapEquiv L₁ (comapEquiv L₂ g) := by
  induction g using induction_on with
  | h f hf => rfl

theorem map_comapEquiv_trans (L₁ : E ≃L[ℂ] F) (L₂ : F ≃L[ℂ] G) (I : Ideal (HolGerm G)) :
    I.map (comapEquiv (L₁.trans L₂)) = (I.map (comapEquiv L₂)).map (comapEquiv L₁) := by
  ext g
  simp only [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨comapEquiv L₂ x, ⟨x, hx, rfl⟩, (comapEquiv_trans_apply L₁ L₂ x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, comapEquiv_trans_apply L₁ L₂ x⟩

theorem map_comapEquiv_refl (I : Ideal (HolGerm E)) :
    I.map (comapEquiv (ContinuousLinearEquiv.refl ℂ E)) = I := by
  ext g
  simp only [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (comap_id x).symm ▸ hx
  · intro hg
    exact ⟨g, hg, comap_id g⟩

end General

/-! ### Products `E × ℂ` -/

section Prod

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Weierstrass polynomial `t ^ s + ∑_{j<s} A_j(z) t ^ j` on `E × ℂ`. -/
def prodWeierstrassGerm (s : ℕ) (A : ℕ → HolGerm E) : HolGerm (E × ℂ) :=
  lastCoord ^ s + ∑ j ∈ Finset.range s, ofFst (A j) * lastCoord ^ j

theorem ofFst_mk (f : E → ℂ) (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) :
    ofFst (mk f hf) = mk (fun x : E × ℂ => f x.1)
      (eventually_differentiableAt_comp_clm (ContinuousLinearMap.fst ℂ E ℂ) hf) :=
  rfl

theorem eventually_differentiableAt_lastPoly (s : ℕ) (a : ℕ → E → ℂ)
    (ha : ∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (a j) z) :
    ∀ᶠ x in 𝓝 (0 : E × ℂ),
      DifferentiableAt ℂ (fun x : E × ℂ => ∑ j ∈ Finset.range s, a j x.1 * x.2 ^ j) x := by
  have hsnd : ∀ᶠ x in 𝓝 (0 : E × ℂ), DifferentiableAt ℂ (fun x : E × ℂ => x.2) x :=
    Eventually.of_forall fun _ => differentiableAt_snd
  exact eventually_differentiableAt_sum _ fun j =>
    eventually_differentiableAt_mul
      (eventually_differentiableAt_comp_clm (ContinuousLinearMap.fst ℂ E ℂ) (ha j))
      (eventually_differentiableAt_pow hsnd j)

theorem eventually_differentiableAt_lastWeierstrass (s : ℕ) (a : ℕ → E → ℂ)
    (ha : ∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (a j) z) :
    ∀ᶠ x in 𝓝 (0 : E × ℂ), DifferentiableAt ℂ
      (fun x : E × ℂ => x.2 ^ s + ∑ j ∈ Finset.range s, a j x.1 * x.2 ^ j) x :=
  eventually_differentiableAt_add
    (eventually_differentiableAt_pow (Eventually.of_forall fun _ => differentiableAt_snd) s)
    (eventually_differentiableAt_lastPoly s a ha)

theorem lastCoord_pow_eq_mk (s : ℕ) :
    (lastCoord : HolGerm (E × ℂ)) ^ s = mk (fun x : E × ℂ => x.2 ^ s)
      (eventually_differentiableAt_pow (Eventually.of_forall fun _ => differentiableAt_snd) s) :=
  (mk_pow _ _ s).symm

theorem sum_ofFst_mul_lastCoord_pow_eq_mk (s : ℕ) (a : ℕ → E → ℂ)
    (ha : ∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (a j) z) :
    ∑ j ∈ Finset.range s, ofFst (mk (a j) (ha j)) * (lastCoord : HolGerm (E × ℂ)) ^ j =
      mk (fun x : E × ℂ => ∑ j ∈ Finset.range s, a j x.1 * x.2 ^ j)
        (eventually_differentiableAt_lastPoly s a ha) := by
  have hterm : ∀ j, ∀ᶠ x in 𝓝 (0 : E × ℂ),
      DifferentiableAt ℂ (fun x : E × ℂ => a j x.1 * x.2 ^ j) x := fun j =>
    eventually_differentiableAt_mul
      (eventually_differentiableAt_comp_clm (ContinuousLinearMap.fst ℂ E ℂ) (ha j))
      (eventually_differentiableAt_pow (Eventually.of_forall fun _ => differentiableAt_snd) j)
  rw [mk_sum (Finset.range s) (fun j (x : E × ℂ) => a j x.1 * x.2 ^ j) hterm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lastCoord_pow_eq_mk]
  rfl

theorem prodWeierstrassGerm_eq_mk (s : ℕ) (a : ℕ → E → ℂ)
    (ha : ∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (a j) z) :
    prodWeierstrassGerm s (fun j => mk (a j) (ha j)) =
      mk (fun x : E × ℂ => x.2 ^ s + ∑ j ∈ Finset.range s, a j x.1 * x.2 ^ j)
        (eventually_differentiableAt_lastWeierstrass s a ha) := by
  rw [prodWeierstrassGerm, sum_ofFst_mul_lastCoord_pow_eq_mk, lastCoord_pow_eq_mk, ← mk_add]

/-- **Weierstrass preparation, germ form.**  After a linear change of coordinates of
`E × ℂ`, a unit multiple of a nonzero germ is a Weierstrass polynomial in the last
variable. -/
theorem exists_mul_comapEquiv_eq_prodWeierstrassGerm {g : HolGerm (E × ℂ)} (hg : g ≠ 0) :
    ∃ (L : (E × ℂ) ≃L[ℂ] E × ℂ) (q : HolGerm (E × ℂ)) (s : ℕ) (A : ℕ → HolGerm E),
      IsUnit q ∧ (∀ j < s, eval (A j) = 0) ∧ q * comapEquiv L g = prodWeierstrassGerm s A := by
  obtain ⟨G, hG, rfl⟩ := exists_eq_mk g
  have hne : ¬ G =ᶠ[𝓝 0] 0 := fun h => hg (by rw [← mk_zero, mk_eq_mk_iff]; exact h)
  obtain ⟨L, d, u, hu, hu0, hLu⟩ :=
    exists_regular_continuousLinearEquiv hG hne (e := ((0 : E), (1 : ℂ))) (by simp)
  have hGL := eventually_differentiableAt_comp_clm (L : (E × ℂ) →L[ℂ] E × ℂ) hG
  have hreg : ∀ᶠ t in 𝓝 (0 : ℂ), (G ∘ L) (0, t) = t ^ d * u t := by
    filter_upwards [hLu] with t ht
    have e : t • ((0 : E), (1 : ℂ)) = ((0 : E), t) := by
      ext <;> simp
    rw [e] at ht
    exact ht
  obtain ⟨q, hq, hq0, a, ha, ha0, heq⟩ := exists_weierstrass_preparation hGL hu hu0 hreg
  refine ⟨L, mk q hq, d, fun j => mk (a j) (ha j), (isUnit_iff_eval_ne_zero _).2 hq0,
    fun j hj => ha0 j hj, ?_⟩
  rw [prodWeierstrassGerm_eq_mk, comapEquiv_mk]
  exact (mk_eq_mk_iff (hf := eventually_differentiableAt_mul hq hGL)).2 heq

/-- **Weierstrass division, germ form**, by a Weierstrass polynomial in the last variable of
`E × ℂ`. -/
theorem exists_eq_mul_prodWeierstrassGerm_add {s : ℕ} {A : ℕ → HolGerm E}
    (hA : ∀ j < s, eval (A j) = 0) (f : HolGerm (E × ℂ)) :
    ∃ (q : HolGerm (E × ℂ)) (r : ℕ → HolGerm E),
      f = q * prodWeierstrassGerm s A + ∑ j ∈ Finset.range s, ofFst (r j) * lastCoord ^ j := by
  choose a ha hAa using fun j => exists_eq_mk (A j)
  obtain rfl : A = fun j => mk (a j) (ha j) := funext hAa
  obtain ⟨h, hh, rfl⟩ := exists_eq_mk f
  have hW := eventually_differentiableAt_lastWeierstrass s a ha
  have hreg : ∀ᶠ t in 𝓝 (0 : ℂ),
      (fun x : E × ℂ => x.2 ^ s + ∑ j ∈ Finset.range s, a j x.1 * x.2 ^ j) (0, t) =
        t ^ s * (fun _ => (1 : ℂ)) t := by
    refine Eventually.of_forall fun t => ?_
    have h0 : ∑ j ∈ Finset.range s, a j 0 * t ^ j = 0 :=
      Finset.sum_eq_zero fun j hj => by
        rw [show a j 0 = 0 from hA j (Finset.mem_range.1 hj), zero_mul]
    simp only [h0, add_zero, mul_one]
  obtain ⟨q, hq, r, hr, heq⟩ :=
    germWeierstrassDivision E _ hW s (fun _ => 1) analyticAt_const one_ne_zero hreg h hh
  refine ⟨mk q hq, fun j => mk (r j) (hr j), ?_⟩
  rw [prodWeierstrassGerm_eq_mk, sum_ofFst_mul_lastCoord_pow_eq_mk, ← mk_mul, ← mk_add,
    mk_eq_mk_iff]
  exact heq

/-! ### Linear changes of the first factor -/

theorem comapEquiv_prodCongr_ofFst (L : E ≃L[ℂ] E) (x : HolGerm E) :
    comapEquiv (L.prodCongr (ContinuousLinearEquiv.refl ℂ ℂ)) (ofFst x) =
      ofFst (comapEquiv L x) := by
  induction x using induction_on with
  | h f hf => rfl

theorem comapEquiv_prodCongr_lastCoord (L : E ≃L[ℂ] E) :
    comapEquiv (L.prodCongr (ContinuousLinearEquiv.refl ℂ ℂ)) (lastCoord : HolGerm (E × ℂ)) =
      lastCoord :=
  rfl

theorem comapEquiv_prodCongr_prodWeierstrassGerm (L : E ≃L[ℂ] E) (s : ℕ) (A : ℕ → HolGerm E) :
    comapEquiv (L.prodCongr (ContinuousLinearEquiv.refl ℂ ℂ)) (prodWeierstrassGerm s A) =
      prodWeierstrassGerm s (fun j => comapEquiv L (A j)) := by
  simp only [prodWeierstrassGerm, map_add, map_pow, map_sum, map_mul,
    comapEquiv_prodCongr_ofFst, comapEquiv_prodCongr_lastCoord]

theorem comap_ofFst_map_comapEquiv_prodCongr (L : E ≃L[ℂ] E) (I : Ideal (HolGerm (E × ℂ))) :
    (I.map (comapEquiv (L.prodCongr (ContinuousLinearEquiv.refl ℂ ℂ)))).comap ofFst =
      (I.comap ofFst).map (comapEquiv L) := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_map_of_equiv, Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨y, hy, hyx⟩
    refine ⟨(comapEquiv L).symm x, ?_, by simp⟩
    rw [Ideal.mem_comap]
    convert hy using 1
    apply (comapEquiv (L.prodCongr (ContinuousLinearEquiv.refl ℂ ℂ))).injective
    rw [hyx, comapEquiv_prodCongr_ofFst, RingEquiv.apply_symm_apply]
  · rintro ⟨y, hy, rfl⟩
    exact ⟨ofFst y, hy, comapEquiv_prodCongr_ofFst L y⟩

end Prod

/-! ### The coordinate tower `𝒪_k ⊆ 𝒪_n` -/

section Tower

/-- The inclusion `𝒪_k → 𝒪_n` induced by the projection `ℂⁿ → ℂᵏ` onto the first `k`
coordinates. -/
def projGerm (n k : ℕ) : HolGerm (ComplexModel k) →+* HolGerm (ComplexModel n) :=
  comap (coordinateProjection n k)

/-- The germ of the coordinate `z_k` on `ℂⁿ` (`0`-indexed, `k < n`). -/
def coordGerm (n k : ℕ) (hk : k < n) : HolGerm (ComplexModel n) :=
  mk (EuclideanSpace.proj (⟨k, hk⟩ : Fin n) : ComplexModel n →L[ℂ] ℂ)
    (Eventually.of_forall fun _ => ContinuousLinearMap.differentiableAt _)

/-- The Weierstrass polynomial `z_k ^ s + ∑_{j<s} A_j(z_0, …, z_{k-1}) z_k ^ j` on `ℂⁿ`,
with coefficients `A_j ∈ 𝒪_k`.  It is a Weierstrass polynomial when `A_j(0) = 0`. -/
def weierstrassGerm (n k : ℕ) (hk : k < n) (s : ℕ) (A : ℕ → HolGerm (ComplexModel k)) :
    HolGerm (ComplexModel n) :=
  coordGerm n k hk ^ s + ∑ j ∈ Finset.range s, projGerm n k (A j) * coordGerm n k hk ^ j

theorem projGerm_mk (n k : ℕ) (f : ComplexModel k → ℂ)
    (hf : ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ f z) :
    projGerm n k (mk f hf) = mk (fun z => f (coordinateProjection n k z))
      (eventually_differentiableAt_comp_clm (coordinateProjection n k) hf) :=
  rfl

theorem coordinateProjection_self (n : ℕ) :
    coordinateProjection n n = ContinuousLinearMap.id ℂ (ComplexModel n) := by
  ext z a
  simp [coordinateProjection_apply]

theorem coordinateProjection_comp {d n m : ℕ} (hdn : d ≤ n) :
    (coordinateProjection n d).comp (coordinateProjection m n) = coordinateProjection m d := by
  ext z a
  have ha : a.1 < n := lt_of_lt_of_le a.2 hdn
  simp [coordinateProjection_apply, ha]

theorem projGerm_self (n : ℕ) (c : HolGerm (ComplexModel n)) : projGerm n n c = c := by
  rw [projGerm, coordinateProjection_self, comap_id]

theorem projGerm_projGerm {d n m : ℕ} (hdn : d ≤ n) (c : HolGerm (ComplexModel d)) :
    projGerm m n (projGerm n d c) = projGerm m d c := by
  rw [projGerm, projGerm, projGerm, comap_comap, coordinateProjection_comp hdn]

/-- `𝒪_k → 𝒪_n` is injective for `k ≤ n`. -/
theorem projGerm_injective {n k : ℕ} (hk : k ≤ n) : Function.Injective (projGerm n k) := by
  intro x y hxy
  have key : ∀ c : HolGerm (ComplexModel k),
      comap (coordinateInclusion n k) (projGerm n k c) = c := by
    intro c
    have hcomp : (coordinateProjection n k).comp (coordinateInclusion n k) =
        ContinuousLinearMap.id ℂ (ComplexModel k) := by
      ext w : 1
      exact coordinateProjection_coordinateInclusion hk w
    rw [projGerm, comap_comap, hcomp, comap_id]
  rw [← key x, ← key y, hxy]

theorem projGerm_coordGerm {n m k : ℕ} (hk : k < n) (hnm : n ≤ m) :
    projGerm m n (coordGerm n k hk) = coordGerm m k (lt_of_lt_of_le hk hnm) := by
  rw [coordGerm, projGerm_mk, coordGerm, mk_eq_mk_iff]
  refine Eventually.of_forall fun z => ?_
  simp [coordinateProjection_apply, lt_of_lt_of_le hk hnm]

theorem projGerm_weierstrassGerm {n m k : ℕ} (hk : k < n) (hnm : n ≤ m) (s : ℕ)
    (A : ℕ → HolGerm (ComplexModel k)) :
    projGerm m n (weierstrassGerm n k hk s A) =
      weierstrassGerm m k (lt_of_lt_of_le hk hnm) s A := by
  simp only [weierstrassGerm, map_add, map_pow, map_sum, map_mul, projGerm_coordGerm hk hnm,
    projGerm_projGerm hk.le]

theorem comapEquiv_euclideanSnocCLE_ofFst (n : ℕ) (x : HolGerm (ComplexModel n)) :
    comapEquiv (euclideanSnocCLE n) (ofFst x) = projGerm (n + 1) n x := by
  induction x using induction_on with
  | h f hf =>
    refine (mk_eq_mk_iff (f := fun z => f (euclideanSnocCLE n z).1)
      (g := fun z => f (coordinateProjection (n + 1) n z))
      (hf := eventually_differentiableAt_comp_clm
        ((ContinuousLinearMap.fst ℂ (ComplexModel n) ℂ).comp
          (euclideanSnocCLE n : ComplexModel (n + 1) →L[ℂ] ComplexModel n × ℂ)) hf)
      (hg := eventually_differentiableAt_comp_clm (coordinateProjection (n + 1) n) hf)).2 ?_
    refine Eventually.of_forall fun z => ?_
    simp only
    congr 1
    ext a
    simp [coordinateProjection_apply, euclideanSnocCLE, Fin.castSucc]
    rfl

theorem comapEquiv_euclideanSnocCLE_lastCoord (n : ℕ) :
    comapEquiv (euclideanSnocCLE n) (lastCoord : HolGerm (ComplexModel n × ℂ)) =
      coordGerm (n + 1) n n.lt_succ_self := by
  refine (mk_eq_mk_iff (f := fun z => (euclideanSnocCLE n z).2)
    (g := (EuclideanSpace.proj (⟨n, n.lt_succ_self⟩ : Fin (n + 1)) : ComplexModel (n + 1) →L[ℂ] ℂ))
    (hf := Eventually.of_forall fun _ => ((ContinuousLinearMap.snd ℂ (ComplexModel n) ℂ).comp
          (euclideanSnocCLE n : ComplexModel (n + 1) →L[ℂ] ComplexModel n × ℂ)).differentiableAt)
    (hg := Eventually.of_forall fun _ => ContinuousLinearMap.differentiableAt _)).2 ?_
  refine Eventually.of_forall fun z => ?_
  simp [euclideanSnocCLE, Fin.last]

theorem comapEquiv_euclideanSnocCLE_prodWeierstrassGerm (n s : ℕ)
    (A : ℕ → HolGerm (ComplexModel n)) :
    comapEquiv (euclideanSnocCLE n) (prodWeierstrassGerm s A) =
      weierstrassGerm (n + 1) n n.lt_succ_self s A := by
  simp only [prodWeierstrassGerm, weierstrassGerm, map_add, map_pow, map_sum, map_mul,
    comapEquiv_euclideanSnocCLE_ofFst, comapEquiv_euclideanSnocCLE_lastCoord]

/-- **Weierstrass division on `ℂ^{n+1}`** by a Weierstrass polynomial in the last
coordinate: `f = q W + ∑_{j<s} r_j z_n ^ j` with `r_j ∈ 𝒪_n`. -/
theorem exists_eq_mul_weierstrassGerm_add {n s : ℕ} {A : ℕ → HolGerm (ComplexModel n)}
    (hA : ∀ j < s, eval (A j) = 0) (f : HolGerm (ComplexModel (n + 1))) :
    ∃ (q : HolGerm (ComplexModel (n + 1))) (r : ℕ → HolGerm (ComplexModel n)),
      f = q * weierstrassGerm (n + 1) n n.lt_succ_self s A +
        ∑ j ∈ Finset.range s, projGerm (n + 1) n (r j) * coordGerm (n + 1) n n.lt_succ_self ^ j :=
          by
  obtain ⟨q, r, h⟩ :=
    exists_eq_mul_prodWeierstrassGerm_add hA ((comapEquiv (euclideanSnocCLE n)).symm f)
  refine ⟨comapEquiv (euclideanSnocCLE n) q, r, ?_⟩
  have h' := congrArg (comapEquiv (euclideanSnocCLE n)) h
  simpa only [RingEquiv.apply_symm_apply, map_add, map_mul, map_sum, map_pow,
    comapEquiv_euclideanSnocCLE_prodWeierstrassGerm, comapEquiv_euclideanSnocCLE_ofFst,
    comapEquiv_euclideanSnocCLE_lastCoord] using h'

/-- The linear map `z ↦ ((z_0, …, z_{k-1}), z_k)` from `ℂⁿ` to `ℂᵏ × ℂ`. -/
def coordSplit (n k : ℕ) (hk : k < n) : ComplexModel n →L[ℂ] ComplexModel k × ℂ :=
  (coordinateProjection n k).prod
    (EuclideanSpace.proj (⟨k, hk⟩ : Fin n) : ComplexModel n →L[ℂ] ℂ)

theorem comap_coordSplit_ofFst (n k : ℕ) (hk : k < n) (x : HolGerm (ComplexModel k)) :
    comap (coordSplit n k hk) (ofFst x) = projGerm n k x := by
  rw [ofFst, comap_comap]
  rfl

theorem comap_coordSplit_lastCoord (n k : ℕ) (hk : k < n) :
    comap (coordSplit n k hk) (lastCoord : HolGerm (ComplexModel k × ℂ)) = coordGerm n k hk :=
  rfl

theorem comap_coordSplit_prodWeierstrassGerm (n k : ℕ) (hk : k < n) (s : ℕ)
    (A : ℕ → HolGerm (ComplexModel k)) :
    comap (coordSplit n k hk) (prodWeierstrassGerm s A) = weierstrassGerm n k hk s A := by
  simp only [prodWeierstrassGerm, weierstrassGerm, map_add, map_pow, map_sum, map_mul,
    comap_coordSplit_ofFst, comap_coordSplit_lastCoord]

theorem eventually_differentiableAt_coordWeierstrass (n k : ℕ) (hk : k < n) (s : ℕ)
    (a : ℕ → ComplexModel k → ℂ) (ha : ∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (a j) z) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ (fun z : ComplexModel n =>
      z ⟨k, hk⟩ ^ s + ∑ j ∈ Finset.range s, a j (coordinateProjection n k z) * z ⟨k, hk⟩ ^ j) z :=
  eventually_differentiableAt_comp_clm (coordSplit n k hk)
    (eventually_differentiableAt_lastWeierstrass s a ha)

/-- The Weierstrass germ with coefficient germs `mk (a j)` is the germ of the explicit
function `z_k ^ s + ∑_{j<s} a_j(z_0, …, z_{k-1}) z_k ^ j`. -/
theorem weierstrassGerm_eq_mk (n k : ℕ) (hk : k < n) (s : ℕ) (a : ℕ → ComplexModel k → ℂ)
    (ha : ∀ j, ∀ᶠ z in 𝓝 0, DifferentiableAt ℂ (a j) z) :
    weierstrassGerm n k hk s (fun j => mk (a j) (ha j)) =
      mk (fun z : ComplexModel n =>
        z ⟨k, hk⟩ ^ s + ∑ j ∈ Finset.range s, a j (coordinateProjection n k z) * z ⟨k, hk⟩ ^ j)
        (eventually_differentiableAt_coordWeierstrass n k hk s a ha) := by
  rw [← comap_coordSplit_prodWeierstrassGerm, prodWeierstrassGerm_eq_mk, comap_mk]
  rfl

end Tower

end HolGerm

end

end SGPT.Foundations.Analysis.Pending
