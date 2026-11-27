/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.StageFiniteProbability
public import LeanPool.KLRandomness.AffineCodeCoverage

/-!
# Effective reconstruction of a bounded affine event

An affine block with bounded support can be output as a certified ordinary
code by exhaustive finite truth-table comparison. This avoids treating a
noncomputably chosen matrix representation as part of the reconstruction
program. The input to the program is only the rank, a coordinate bound, and
the parameters of a computable Boolean predicate on prefixes.
-/

@[expose] public section

namespace Klr.StageCodeSearch

open AffineCode FiniteMeasure SparseSearch

/-- Every affine block whose support lies below `n` has a certified code of
exactly that width. The witness is used to prove search termination. -/
theorem exists_valid_code_bounded (B : AffineBlock) (n : ℕ)
    (hn : ∀ k ∈ B.support, k < n) :
    ∃ c : Data, width c = n ∧ rank c = B.rank ∧ valid c = true ∧ event c = B.event := by
  classical
  let restrict : (Fin n → ZMod 2) →ₗ[ZMod 2] (B.support → ZMod 2) :=
    { toFun := fun x i => x ⟨i.val, hn i.val i.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hrestrict : Function.Surjective restrict := by
    intro x
    refine ⟨fun j => if hj : j.val ∈ B.support then x ⟨j.val, hj⟩ else 0, ?_⟩
    funext i
    change (if hi : i.val ∈ B.support then x ⟨i.val, hi⟩ else 0) = x i
    simp [i.property]
  let D := B.matrix.comp restrict
  let A := LinearMap.toMatrix' D
  have hA : Function.Surjective A.mulVecLin := by
    intro y
    obtain ⟨x, hx⟩ := B.fullRank y
    obtain ⟨v, hv⟩ := hrestrict x
    refine ⟨v, ?_⟩
    change Matrix.mulVec (LinearMap.toMatrix' D) v = y
    rw [LinearMap.toMatrix'_mulVec]
    change B.matrix (restrict v) = y
    rw [hv, hx]
  obtain ⟨c, hw, hr, hv, he⟩ := exists_valid_code A hA B.syndrome
  refine ⟨c, hw, hr, hv, he.trans ?_⟩
  ext X
  change Matrix.mulVec (LinearMap.toMatrix' D)
    (coordinateValues (fun i : Fin n => i.val) X) = B.syndrome ↔ _
  rw [LinearMap.toMatrix'_mulVec]
  rfl

/-- The finite verifier requires both a right-inverse certificate and exact
agreement with the target truth table. -/
def check (r n : ℕ) (p : List Bool → Bool) (c : Data) : Bool :=
  valid c && (decide (rank c = r) && (decide (width c ≤ n) &&
    (words n).all (fun s => decide (accepts c s = p s))))

theorem check_eq_true (r n : ℕ) (p : List Bool → Bool) (c : Data) :
    check r n p c = true ↔ valid c = true ∧ rank c = r ∧ width c ≤ n ∧
      ∀ s, s.length = n → accepts c s = p s := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, mem_words_iff]

theorem computable_check {α : Type*} [Primcodable α]
    {r n : α → ℕ} {p : α → List Bool → Bool}
    (hr : Computable r) (hn : Computable n) (hp : Computable₂ p) :
    Computable₂ (fun a c => check (r a) (n a) (p a) c) := by
  have hc : Computable (fun z : (α × Data) × List Bool => z.1.2) :=
    Computable.snd.comp Computable.fst
  have ht := Primrec.eq.decide.to_comp.comp
    (computable_accepts.comp hc Computable.snd)
    (hp.comp (Computable.fst.comp Computable.fst) Computable.snd)
  have hall := computable_list_all
    (p := fun z : α × Data => fun s => decide (accepts z.2 s = p z.1 s))
    (computable_words.comp (hn.comp Computable.fst)) ht.to₂
  have hwidth := Primrec.nat_le.decide.to_comp.comp
    (computable_width.comp Computable.snd) (hn.comp Computable.fst)
  have hrank := Primrec.eq.decide.to_comp.comp
    (computable_rank.comp Computable.snd) (hr.comp Computable.fst)
  exact Primrec.and.to_comp.comp (computable_valid.comp Computable.snd)
    (Primrec.and.to_comp.comp hrank (Primrec.and.to_comp.comp hwidth hall))

/-- Decode a candidate number and return its affine code if it passes the checks. -/
def trial (r n : ℕ) (p : List Bool → Bool) (k : ℕ) : Option Data :=
  (Encodable.decode k).bind (fun c => if check r n p c then some c else none)

/-- Search for the first coded affine system that satisfies the target finite test. -/
def reconstruct (r n : ℕ) (p : List Bool → Bool) : Part Data :=
  Nat.rfindOpt (trial r n p)

theorem computable_trial {α : Type*} [Primcodable α]
    {r n : α → ℕ} {p : α → List Bool → Bool}
    (hr : Computable r) (hn : Computable n) (hp : Computable₂ p) :
    Computable₂ (fun a k => trial (r a) (n a) (p a) k) := by
  have hc := computable_check hr hn hp
  have hf : Computable₂ (fun a c => if check (r a) (n a) (p a) c then some c else none) := by
    exact (Computable.cond hc (Computable.option_some.comp Computable.snd)
      (Computable.const none)).of_eq fun _ => by simp only [Bool.cond_eq_ite]
  exact Computable.bind_decode_iff.mpr hf

/-- A single partial recursive reconstruction algorithm works for every
computable family of target finite truth tables. -/
theorem partrec_reconstruct {α : Type*} [Primcodable α]
    {r n : α → ℕ} {p : α → List Bool → Bool}
    (hr : Computable r) (hn : Computable n) (hp : Computable₂ p) :
    Partrec (fun a => reconstruct (r a) (n a) (p a)) :=
  Partrec.rfindOpt (computable_trial hr hn hp)

theorem reconstruct_spec {r n : ℕ} {p : List Bool → Bool} {c : Data}
    (hc : c ∈ reconstruct r n p) :
    valid c = true ∧ rank c = r ∧ width c ≤ n ∧
      ∀ s, s.length = n → accepts c s = p s := by
  obtain ⟨k, hk⟩ := Nat.rfindOpt_spec hc
  simp only [trial, Option.mem_bind_iff] at hk
  obtain ⟨d, _, hd⟩ := hk
  split_ifs at hd with hv
  · have he : d = c := Option.mem_some_iff.mp hd
    subst d
    exact (check_eq_true r n p c).mp hv
  · simp at hd

theorem inputPrefix_getD (s : List Bool) :
    ScanRule.inputPrefix (fun k => s.getD k false) s.length = s := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  rw [← List.getD_eq_getElem _ false hi, ← List.getD_eq_getElem _ false hj,
    ScanRule.getD_inputPrefix _ (by simpa using hi)]

/-- The algorithm halts for an actual bounded affine block and returns exactly
its event, at exactly its rank, with a checked right-inverse certificate. -/
theorem exists_reconstructed_code (B : AffineBlock) (n : ℕ)
    (hn : ∀ k ∈ B.support, k < n) (p : List Bool → Bool)
    (hp : ∀ X, p (ScanRule.inputPrefix X n) = true ↔ X ∈ B.event) :
    ∃ c ∈ reconstruct B.rank n p,
      valid c = true ∧ rank c = B.rank ∧ event c = B.event := by
  obtain ⟨d, hdw, hdr, hdv, hde⟩ := exists_valid_code_bounded B n hn
  have hcheck : check B.rank n p d = true := by
    apply (check_eq_true _ _ _ _).mpr
    refine ⟨hdv, hdr, hdw.le, ?_⟩
    intro s hs
    rw [Bool.eq_iff_iff]
    have hx := StageFiniteProbability.accepts_code_inputPrefix d n hdw.le
      (fun k => s.getD k false)
    have hxp := hp (fun k => s.getD k false)
    rw [← hs, inputPrefix_getD] at hx hxp
    exact hx.trans (hde ▸ hxp.symm)
  have hdom : (reconstruct B.rank n p).Dom := by
    apply Nat.rfindOpt_dom.mpr
    refine ⟨Encodable.encode d, d, ?_⟩
    simp [trial, hcheck]
  obtain ⟨c, hc⟩ := Part.dom_iff_mem.mp hdom
  obtain ⟨hcv, hcr, hcw, hcp⟩ := reconstruct_spec hc
  refine ⟨c, hc, hcv, hcr, ?_⟩
  ext X
  rw [← StageFiniteProbability.accepts_code_inputPrefix c n hcw X,
    hcp _ (ScanRule.length_inputPrefix X n)]
  exact hp X

end Klr.StageCodeSearch
