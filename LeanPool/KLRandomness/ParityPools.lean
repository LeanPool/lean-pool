/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.PoolConstruction
public import LeanPool.KLRandomness.StageReconstruction
public import LeanPool.KLRandomness.PairRespecting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Common Borel partitions for even and odd pools

Two auxiliary scans reading only even positions force the existing weighted
pool construction to select even pools. A pair-respecting scan eventually
reads an even position precisely when it reads its odd partner, so shifting
the completed pool preserves both missed-position estimates. The auxiliary
scans are used only in the pool argument.
-/

@[expose] public section

namespace Klr.ParityPools

open Filter MeasureTheory PoolConstruction
open scoped Topology BigOperators

/-- A computable scan which reads all even positions in order. -/
def evenScan : ScanRule where
  query v := 2 * v.length
  computable_query := Primrec.nat_mul.to_comp.comp (Computable.const 2) Computable.list_length
  fresh := by
    intro v n hn
    simp only [List.length_take, Nat.min_eq_left hn.le]
    omega

@[simp] theorem reads_evenScan (a : ℕ) (Z : Cantor) :
    PoolQuery.Reads evenScan a Z ↔ a % 2 = 0 := by
  change (∃ t, 2 * (ScanRule.inputPrefix Z t).length = a) ↔ _
  simp only [ScanRule.inputPrefix, List.length_map, List.length_range]
  constructor
  · rintro ⟨t, rfl⟩
    omega
  · intro ha
    exact ⟨a / 2, by omega⟩

theorem queryProbability_evenScan (a : ℕ) :
    Pool.queryProbability evenScan a = if a % 2 = 0 then 1 else 0 := by
  rw [Pool.queryProbability_eq_measureReal]
  by_cases ha : a % 2 = 0 <;> simp [ha]

/-- The two auxiliary weights sum to three quarters. -/
def augmented (π : ℕ → ScanRule) : ℕ → ScanRule
  | 0 => evenScan
  | 1 => evenScan
  | i + 2 => π i

theorem weighted_even_lower (π : ℕ → ScanRule) {a : ℕ} (ha : a % 2 = 0) :
    (3 / 4 : ℝ) ≤ Pool.weightedQueryProbability (augmented π) a := by
  have h := (Pool.weighted_query_truncation (augmented π) a 2).1
  norm_num [Finset.sum_range_succ, augmented, Pool.weight, queryProbability_evenScan, ha] at h
  linarith

theorem weighted_odd_upper (π : ℕ → ScanRule) {a : ℕ} (ha : a % 2 ≠ 0) :
    Pool.weightedQueryProbability (augmented π) a ≤ (1 / 4 : ℝ) := by
  have h := (Pool.weighted_query_truncation (augmented π) a 2).2
  norm_num [Finset.sum_range_succ, augmented, Pool.weight, queryProbability_evenScan, ha] at h
  exact h

theorem limsup_gt_half (π : ℕ → ScanRule) :
    (1 / 2 : ℝ) < Pool.weightedQueryLimsup (augmented π) := by
  obtain ⟨z, hz⟩ := Pool.exists_weighted_query_upper_cutoff (augmented π)
    (show (0 : ℝ) < 1 / 8 by norm_num)
  have hu := hz (2 * z) (by omega)
  have hl := weighted_even_lower π (a := 2 * z) (by omega)
  linarith

theorem eventually_even {π : ℕ → ScanRule} {a : ℕ → ℕ}
    (Q : Pool.QueryPartition (augmented π) a)
    (hp : Tendsto (Pool.weightedQueryProbability (augmented π) ∘ Q.position) atTop
      (𝓝 (Pool.weightedQueryLimsup (augmented π)))) :
    ∀ᶠ n : ℕ in atTop, Q.position n % 2 = 0 := by
  have he := hp.eventually (lt_mem_nhds (limsup_gt_half π))
  filter_upwards [he] with n hn
  by_contra hodd
  have h := weighted_odd_upper π hodd
  dsimp only [Function.comp_def] at hn
  linarith

/-- The first dummy scan has a full-measure high set. -/
theorem high_zero_measure {π : ℕ → ScanRule} {a : ℕ → ℕ}
    (Q : Pool.QueryPartition (augmented π) a)
    (hp : Tendsto (Pool.weightedQueryProbability (augmented π) ∘ Q.position) atTop
      (𝓝 (Pool.weightedQueryLimsup (augmented π)))) :
    fairCoin.real (Q.high 0) = 1 := by
  have hq : (fun n => Pool.queryProbability (augmented π 0) (Q.position n))
      =ᶠ[atTop] (fun _ => (1 : ℝ)) := by
    filter_upwards [eventually_even Q hp] with n hn
    simp [augmented, queryProbability_evenScan, hn]
  have hi : (∫ Z, Q.limit 0 Z ∂fairCoin) = 1 :=
    tendsto_nhds_unique (Q.queryProbability_tendsto 0)
      (tendsto_const_nhds.congr' hq.symm)
  have hrep : Q.representative 0 =ᵐ[fairCoin] (fun _ => (1 : ℝ)) := by
    apply (integral_eq_iff_of_ae_le
      ((Pool.integrable_L2 (Q.limit 0)).congr (Q.representative_ae_eq 0).symm)
      (integrable_const 1)
      (Filter.Eventually.of_forall fun Z => (Q.representative_bounds 0 Z).2)).mp
    rw [Q.integral_representative, hi]
    simp
  have hs : Q.high 0 =ᵐ[fairCoin] Set.univ := by
    filter_upwards [hrep] with Z hZ
    change (Q.representative 0 Z = 1) ↔ (Z ∈ Set.univ)
    simp [hZ]
  rw [measureReal_congr hs]
  simp

/-- Every sufficiently accurate good pool for the augmented family is even. -/
theorem even_of_goodPool {π : ℕ → ScanRule} {H : ℕ → Set Cantor}
    (hH : fairCoin.real (H 0) = 1) {ℓ z M : ℕ} {η : ℝ} {τ : ℚ} {G : List ℕ}
    (hη : η < 1) (hG : GoodPool (augmented π) H (ℓ + 2) η z τ M G) :
    ∀ b ∈ G, b % 2 = 0 := by
  intro b hb
  by_contra hodd
  have hh := (hG.2.2.2 0 (by omega)).1
  have he : {Z | Z ∈ H 0 ∧ ∃ a ∈ G, ¬ PoolQuery.Reads (augmented π 0) a Z} = H 0 := by
    ext Z
    constructor
    · exact And.left
    · intro hZ
      exact ⟨hZ, b, hb, by simpa [augmented] using hodd⟩
  rw [he, hH] at hh
  linarith

theorem strip_goodPool {π : ℕ → ScanRule} {H : ℕ → Set Cantor}
    {ℓ z M : ℕ} {η ε : ℝ} {τ : ℚ} {G : List ℕ} (hη : η ≤ ε)
    (hG : GoodPool (augmented π) H (ℓ + 2) η z τ M G) :
    GoodPool π (fun i => H (i + 2)) ℓ ε z τ M G := by
  refine ⟨hG.1, hG.2.1, hG.2.2.1, ?_⟩
  intro i hi
  have h := hG.2.2.2 (i + 2) (by omega)
  exact ⟨h.1.trans_le hη, h.2.trans_le hη⟩

/-- The existing fixed-advice search can already produce confined even pools. -/
theorem exists_fixed_partitions_even_pools (π : ℕ → ScanRule) :
    ∃ H : ℕ → Set Cantor, (∀ i, MeasurableSet (H i)) ∧
      ∀ (ℓ : ℕ) (η : ℝ), 0 < η → ∀ z : ℕ,
        ∃ τ : ℚ, 0 < τ ∧ τ < 1 / 4 ∧
          ∃ e : Nat.Partrec.Code, ∀ᶠ M : ℕ in atTop,
            ∃ G : List ℕ, PoolAdvice.encodePool G ∈ e.eval M ∧
              GoodPool π H ℓ η z τ M G ∧ ∀ b ∈ G, b % 2 = 0 := by
  obtain ⟨a, Q, ha, hp, _⟩ := Pool.exists_weighted_queryPartition (augmented π)
  refine ⟨fun i => Q.high (i + 2), fun i => Q.measurableSet_high (i + 2), ?_⟩
  intro ℓ η hη z
  let ε := min η (1 / 2 : ℝ)
  have hε : 0 < ε := lt_min hη (by norm_num)
  obtain ⟨P⟩ := PoolAdvice.exists_fixedParameters Q (ℓ + 2) hε z
  obtain ⟨e, he⟩ := FixedParameters.exists_eventual_goodPool_program P ha hp
  refine ⟨P.margin, P.margin_pos, P.margin_lt_quarter, e, ?_⟩
  filter_upwards [he] with M hM
  obtain ⟨G, hcode, hG⟩ := hM
  exact ⟨G, hcode, strip_goodPool (min_le_left _ _) hG,
    even_of_goodPool (high_zero_measure Q hp)
      ((min_le_right _ _).trans_lt (by norm_num)) hG⟩

theorem reads_add_parity {π : ScanRule} (hπ : π.PairRespecting)
    {a c : ℕ} (ha : a % 2 = 0) (hc : c < 2) (Z : Cantor) :
    PoolQuery.Reads π (a + c) Z ↔ PoolQuery.Reads π a Z := by
  have hc' : c = 0 ∨ c = 1 := by omega
  rcases hc' with rfl | rfl
  · simp
  · have he : a = 2 * (a / 2) := by omega
    rw [he]
    exact (hπ.reads_even_iff_reads_odd Z (a / 2)).symm

theorem missedCount_map_add {π : ScanRule} (hπ : π.PairRespecting)
    (G : List ℕ) (hG : ∀ a ∈ G, a % 2 = 0) (c : ℕ) (hc : c < 2) (Z : Cantor) :
    PoolQuery.missedCount π (G.map (· + c)).toFinset Z =
      PoolQuery.missedCount π G.toFinset Z := by
  classical
  have hm : (G.map (· + c)).toFinset = G.toFinset.image (· + c) := by
    ext a
    simp
  simp only [PoolQuery.missedCount, hm, Finset.filter_image]
  have he : G.toFinset.filter (fun a => ¬ PoolQuery.Reads π (a + c) Z) =
      G.toFinset.filter (fun a => ¬ PoolQuery.Reads π a Z) := by
    apply Finset.filter_congr
    intro a ha
    exact not_congr (reads_add_parity hπ (hG a (List.mem_toFinset.mp ha)) hc Z)
  rw [he, Finset.card_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h)]

/-- Translating even pools by either parity preserves the completed infinite
miss events. No equality of finite-horizon hit events is asserted. -/
theorem goodPool_map_add {π : ℕ → ScanRule} (hπ : ∀ i, (π i).PairRespecting)
    {H : ℕ → Set Cantor} {ℓ z M : ℕ} {η : ℝ} {τ : ℚ} {G : List ℕ}
    (hG : GoodPool π H ℓ η z τ M G) (heven : ∀ a ∈ G, a % 2 = 0)
    (c : ℕ) (hc : c < 2) :
    GoodPool π H ℓ η z τ M (G.map (· + c)) := by
  refine ⟨by simpa using hG.1,
    hG.2.1.map (fun _ _ h => Nat.add_right_cancel h), ?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact (hG.2.2.1 b hb).trans (Nat.le_add_right _ _)
  · intro i hi
    have hreads : ∀ Z, (∃ a ∈ G.map (· + c), ¬ PoolQuery.Reads (π i) a Z) ↔
        ∃ a ∈ G, ¬ PoolQuery.Reads (π i) a Z := by
      intro Z
      constructor
      · rintro ⟨a, ha, hm⟩
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        exact ⟨b, hb, (not_congr (reads_add_parity (hπ i) (heven b hb) hc Z)).mp hm⟩
      · rintro ⟨a, ha, hm⟩
        exact ⟨a + c, List.mem_map.mpr ⟨a, ha, rfl⟩,
          (not_congr (reads_add_parity (hπ i) (heven a ha) hc Z)).mpr hm⟩
    simpa only [hreads, missedCount_map_add (hπ i) G heven c hc] using hG.2.2.2 i hi

theorem exists_shifted_program (e : Nat.Partrec.Code) (c : ℕ) :
    ∃ e' : Nat.Partrec.Code, ∀ M G,
      PoolAdvice.encodePool G ∈ e.eval M →
      PoolAdvice.encodePool (G.map (· + c)) ∈ e'.eval M := by
  have hm : Computable (fun G : List ℕ => G.map (· + c)) :=
    (Primrec.list_map Primrec.id
      (Primrec.nat_add.comp Primrec.snd (Primrec.const c)).to₂).to_comp
  let f : ℕ → Part (List ℕ) := fun M =>
    (e.eval M).map (fun k => (StageReconstruction.decodePool k).map (· + c))
  have hf : Partrec f :=
    (Nat.Partrec.Code.eval_part.comp (Computable.const e) Computable.id).map
      ((hm.comp StageReconstruction.computable_decodePool).comp Computable.snd)
  obtain ⟨e', he'⟩ := Nat.Partrec.Code.exists_code.mp hf
  refine ⟨e', ?_⟩
  intro M G hG
  rw [he']
  simp only [Encodable.decode_nat, Part.coe_some, Part.bind_some]
  change PoolAdvice.encodePool (G.map (· + c)) ∈ (f M).map PoolAdvice.encodePool
  apply Part.mem_map
  simpa only [f, StageReconstruction.decodePool_encodePool] using
    Part.mem_map (fun k => (StageReconstruction.decodePool k).map (· + c)) hG

/-- One fixed family of Borel partitions supplies both parity classes, with
the parity selected before choosing the fixed pool program. -/
theorem exists_fixed_partitions_parity_pools (π : ℕ → ScanRule)
    (hπ : ∀ i, (π i).PairRespecting) :
    ∃ H : ℕ → Set Cantor, (∀ i, MeasurableSet (H i)) ∧
      ∀ (ℓ : ℕ) (η : ℝ), 0 < η → ∀ z c : ℕ, c < 2 →
        ∃ τ : ℚ, 0 < τ ∧ τ < 1 / 4 ∧
          ∃ e : Nat.Partrec.Code, ∀ᶠ M : ℕ in atTop,
            ∃ G : List ℕ, PoolAdvice.encodePool G ∈ e.eval M ∧
              GoodPool π H ℓ η z τ M G ∧ ∀ b ∈ G, b % 2 = c := by
  obtain ⟨H, hH, hpool⟩ := exists_fixed_partitions_even_pools π
  refine ⟨H, hH, ?_⟩
  intro ℓ η hη z c hc
  obtain ⟨τ, hτ, hτlt, e, he⟩ := hpool ℓ η hη z
  obtain ⟨e', he'⟩ := exists_shifted_program e c
  refine ⟨τ, hτ, hτlt, e', ?_⟩
  filter_upwards [he] with M hM
  obtain ⟨G, hcode, hG, hGeven⟩ := hM
  refine ⟨G.map (· + c), he' M G hcode, goodPool_map_add hπ hG hGeven c hc, ?_⟩
  intro b hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
  have h := hGeven a ha
  omega

end Klr.ParityPools
