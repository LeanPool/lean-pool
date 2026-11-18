/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted from bjoernkjoshanssen/tt-auto, RequestProject/TT.
This development was edited with Aristotle (Harmonic). Its oracle program
infrastructure is reused from the Apache-2.0 OpenAI degree-rigidity port.
-/

module

public import LeanPool.TruthTableRigidity.Uniform
public import LeanPool.TuringConeRigidity.Effective.FiniteTranscript

/-!
# tt-functionals as functionals with primitive recursive finite approximations

`IsApprox Φ H` says that `H σ n` is a primitive recursive *finite approximation* of `Φ`:
evaluated on a finite partial string `σ` of oracle values it either refuses (`none`) or gives
the correct value `Φ X n` for every `X` compatible with `σ`, and it answers as soon as `σ`
extends a long enough prefix of `X`.

We show `IsTTFunctional Φ ↔ ∃ H, IsApprox Φ H`.
-/

@[expose] public section

namespace TT

open OAI.TuringRigidity Encodable

/-- `σ` is a finite partial string of oracle values compatible with `X`. -/
def Compat (σ : List (Option Bool)) (X : Oracle) : Prop :=
  ∀ i b, σ[i]? = some (some b) → X i = b

/-- `H` is a primitive recursive finite approximation of the functional `Φ`. -/
structure IsApprox (Φ : Oracle → Oracle) (H : List (Option Bool) → ℕ → Option Bool) : Prop where
  primrec : Primrec₂ H
  sound : ∀ X σ n b, Compat σ X → H σ n = some b → Φ X n = b
  complete : ∀ X n, ∃ M, ∀ σ, Compat σ X → (pre X M).map some <+: σ → (H σ n).isSome

theorem getElem?_pre (X : Oracle) (m i : ℕ) :
    (pre X m)[i]? = if i < m then some (X i) else none := by
  simp only [pre, List.getElem?_map]
  split_ifs with h
  · simp [List.getElem?_range h]
  · rw [List.getElem?_eq_none (by simp only [List.length_range]; omega)]
    rfl

theorem length_pre (X : Oracle) (m : ℕ) : (pre X m).length = m := by simp [pre]

theorem compat_pre (X : Oracle) (m : ℕ) : Compat ((pre X m).map some) X := by
  intro i b h
  rw [List.getElem?_map, getElem?_pre] at h
  split_ifs at h <;> simp_all

theorem IsApprox.isTTFunctional {Φ : Oracle → Oracle} {H : List (Option Bool) → ℕ → Option Bool}
    (h : IsApprox Φ H) : IsTTFunctional Φ :=
  isTTFunctional_of_approx h.primrec.to_comp
    (fun X m n b hb => h.sound X _ n b (compat_pre X m) hb)
    (fun X n => let ⟨M, hM⟩ := h.complete X n; ⟨M, hM _ (compat_pre X M) (List.prefix_refl _)⟩)

/-- The partial oracle given by a finite partial string. -/
def plook (σ : List (Option Bool)) (k : ℕ) : Part ℕ := (((σ[k]?).bind id).map bv : Option ℕ)

theorem bv_primrec : Primrec bv :=
  (Primrec.cond Primrec.id (Primrec.const 1) (Primrec.const 0)).of_eq fun b => by
    cases b <;> rfl

theorem plook_partrec : Partrec₂ plook :=
  Computable.ofOption (Primrec.option_map (Primrec.option_bind Primrec.list_getElem?
    (Primrec.snd : Primrec (Prod.snd : (List (Option Bool) × ℕ) × Option Bool → Option Bool)).to₂)
    (bv_primrec.comp Primrec.snd).to₂).to_comp

theorem eval_mono {g g' : ℕ →. ℕ} (h : ∀ k v, v ∈ g k → v ∈ g' k) (c : OracleCode)
    (n v : ℕ) (hv : v ∈ OracleCode.eval g c n) : v ∈ OracleCode.eval g' c n :=
  OracleCode.eval_mono h c n v hv

theorem plook_pre (X : Oracle) (m k : ℕ) :
    plook ((pre X m).map some) k =
      BranchMachine.lookup (UniformOracle.oraclePrefix (fun k => bv (X k)) m) k := by
  simp only [plook, BranchMachine.lookup, UniformOracle.oraclePrefix,
    PrefixComputability.oraclePrefix, List.getElem?_map, getElem?_pre]
  by_cases hk : k < m
  · simp [hk]
  · rw [List.getElem?_eq_none (by simp only [List.length_range]; omega)]
    simp [hk]

/-- Every tt-functional has a primitive recursive finite approximation. -/
theorem IsTTFunctional.exists_approx {Φ : Oracle → Oracle} (h : IsTTFunctional Φ) :
    ∃ H, IsApprox Φ H := by
  obtain ⟨c, hc⟩ := h
  have hp : Partrec₂ fun σ n => OracleCode.eval (plook σ) c n :=
    OracleCode.eval_partrec plook_partrec c
  obtain ⟨d, hd⟩ := partrec_code hp
  let H : List (Option Bool) → ℕ → Option Bool := fun σ n =>
    (((List.range (σ.length + 1)).filterMap fun m =>
      Nat.Partrec.Code.evaln σ.length d (encode (σ.take m, n))).head?).map fun v => v == 1
  refine ⟨H, ?_, ?_, ?_⟩
  · have hinner : Primrec₂ fun (p : List (Option Bool) × ℕ) (m : ℕ) =>
        Nat.Partrec.Code.evaln p.1.length d (encode (p.1.take m, p.2)) :=
      Nat.Partrec.Code.primrec_evaln.comp
        (((Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)).pair (Primrec.const d)).pair
          (Primrec.encode.comp ((Primrec.list_take.comp Primrec.snd
            (Primrec.fst.comp Primrec.fst)).pair (Primrec.snd.comp Primrec.fst))))
    have hlist : Primrec fun p : List (Option Bool) × ℕ => List.range (p.1.length + 1) :=
      Primrec.list_range.comp (Primrec.succ.comp (Primrec.list_length.comp Primrec.fst))
    exact Primrec.option_map (Primrec.list_head?.comp (Primrec.listFilterMap hlist hinner))
      (Primrec.beq.comp Primrec.snd (Primrec.const 1)).to₂
  · intro X σ n b hσ hb
    simp only [H, Option.map_eq_some_iff] at hb
    obtain ⟨v, hv, rfl⟩ := hb
    have hmem : v ∈ (List.range (σ.length + 1)).filterMap fun m =>
        Nat.Partrec.Code.evaln σ.length d (encode (σ.take m, n)) :=
      List.mem_of_mem_head? hv
    obtain ⟨m, -, hm⟩ := List.mem_filterMap.mp hmem
    have h1 : v ∈ OracleCode.eval (plook (σ.take m)) c n := by
      have := Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hm)
      rwa [hd (σ.take m, n)] at this
    have h2 : v ∈ OracleCode.eval (oracleFunction X) c n := by
      refine eval_mono ?_ c n v h1
      intro k w hw
      simp only [plook] at hw
      have hw' : ((σ.take m)[k]?.bind id).map bv = some w := by
        simpa [Part.mem_coe] using hw
      rw [Option.map_eq_some_iff] at hw'
      obtain ⟨b', hb', rfl⟩ := hw'
      rw [Option.bind_eq_some_iff] at hb'
      obtain ⟨o, ho, ho'⟩ := hb'
      simp only [id] at ho'
      subst ho'
      rw [List.getElem?_take] at ho
      split_ifs at ho
      change bv b' ∈ Part.some (bv (X k))
      rw [hσ k b' ho]
      exact Part.mem_some _
    rw [hc X] at h2
    have := Part.mem_some_iff.mp h2
    subst this
    generalize Φ X n = b0
    cases b0 <;> rfl
  · intro X n
    have hv : bv (Φ X n) ∈ OracleCode.eval (oracleFunction X) c n := by
      rw [hc X]; exact Part.mem_some _
    obtain ⟨M₀, hM₀⟩ := OracleCode.eval_finite_use (fun k => bv (X k)) c n (bv (Φ X n)) hv
    have h0 : bv (Φ X n) ∈ d.eval (encode ((pre X M₀).map some, n)) := by
      rw [hd]
      change bv (Φ X n) ∈ OracleCode.eval (plook ((pre X M₀).map some)) c n
      rwa [funext (plook_pre X M₀)]
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp h0
    refine ⟨M₀ + k, fun σ _ hσ => ?_⟩
    have hlen : M₀ + k ≤ σ.length := by
      simpa [length_pre] using hσ.length_le
    have htake : σ.take M₀ = (pre X M₀).map some := by
      have e1 := List.prefix_iff_eq_take.mp hσ
      simp only [List.length_map, length_pre] at e1
      rw [show M₀ = min M₀ (M₀ + k) by omega, ← List.take_take, ← e1]
      simp only [pre, List.map_map]
      rw [← List.map_take, List.take_range, Nat.min_eq_left (by omega)]
    have hev : bv (Φ X n) ∈ Nat.Partrec.Code.evaln σ.length d (encode (σ.take M₀, n)) := by
      rw [htake]
      exact Nat.Partrec.Code.evaln_mono (by omega) hk
    have hmem : bv (Φ X n) ∈ (List.range (σ.length + 1)).filterMap fun m =>
        Nat.Partrec.Code.evaln σ.length d (encode (σ.take m, n)) :=
      List.mem_filterMap.mpr ⟨M₀, List.mem_range.mpr (by omega), hev⟩
    simp only [H, Option.isSome_map]
    cases hh : ((List.range (σ.length + 1)).filterMap fun m =>
        Nat.Partrec.Code.evaln σ.length d (encode (σ.take m, n))) with
    | nil => rw [hh] at hmem; simp at hmem
    | cons a l => simp

theorem isTTFunctional_iff_exists_approx (Φ : Oracle → Oracle) :
    IsTTFunctional Φ ↔ ∃ H, IsApprox Φ H :=
  ⟨IsTTFunctional.exists_approx, fun ⟨_, h⟩ => h.isTTFunctional⟩

end TT
