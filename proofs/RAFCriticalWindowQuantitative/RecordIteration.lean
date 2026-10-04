module

public import proofs.RAFCriticalWindowQuantitative.RecordContraction

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold MeasureTheory unitInterval
open scoped ENNReal

def recordCap (ell : ℕ) : ℕ → ℕ :=
  Nat.rec 2 (fun _ cap => 2*cap+ell)

theorem recordCap_ge_two (ell j : ℕ) : 2 ≤ recordCap ell j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [recordCap] at *; omega

theorem recordCap_exact (ell j : ℕ) : recordCap ell j+ell = 2^j*(2+ell) := by
  induction j with
  | zero => simp [recordCap]
  | succ j ih => simp only [recordCap, pow_succ] at *; nlinarith

theorem recordCap_mono_length {ell L : ℕ} (h : ell ≤ L) (j : ℕ) :
    recordCap ell j ≤ recordCap L j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [recordCap] at *; omega

theorem escapedMissing_antitone (v : List Bool) : Antitone (fun B => escapedMissing B v) := by
  intro B N hBN ω hω
  obtain ⟨w,hw,hg⟩ := hω.1
  exact ⟨⟨w,by omega,hg⟩,
    fun hv => hω.2 (finiteReversibleGenerated_mono_cap hBN hv)⟩

theorem repeated_record_failure (a : I) (v : List Bool) (hv : 0 < v.length) (r : ℕ) :
    infiniteSplitPi a (escapedMissing (recordCap v.length r) v) ≤
      (1-(toNNReal a : ENNReal)^(v.length+1))^r := by
  induction r with
  | zero => simpa only [pow_zero] using (prob_le_one : infiniteSplitPi a (escapedMissing (recordCap v.length 0) v) ≤ 1)
  | succ r ih =>
    calc
      _ ≤ infiniteSplitPi a (escapedMissing (recordCap v.length r) v) *
          (1-(toNNReal a : ENNReal)^(v.length+1)) :=
        escaped_missing_contraction a v hv _ (recordCap_ge_two _ _)
      _ ≤ (1-(toNNReal a : ENNReal)^(v.length+1))^r *
          (1-(toNNReal a : ENNReal)^(v.length+1)) := mul_le_mul' ih le_rfl
      _ = _ := (pow_succ _ _).symm

theorem common_cap_target_failure (a : I) (v : List Bool) (hv : 0 < v.length)
    (L : ℕ) (hvL : v.length ≤ L) (r : ℕ) :
    infiniteSplitPi a (escapedMissing (recordCap L r) v) ≤
      (1-(toNNReal a : ENNReal)^(L+1))^r := by
  have hp : (toNNReal a : ENNReal)^(L+1) ≤ (toNNReal a : ENNReal)^(v.length+1) := by
    apply pow_le_pow_of_le_one (zero_le : 0 ≤ (toNNReal a : ENNReal))
    · exact_mod_cast a.property.2
    · omega
  exact ((measure_mono (escapedMissing_antitone v (recordCap_mono_length hvL r))).trans
    (repeated_record_failure a v hv r)).trans
      (pow_le_pow_left' (tsub_le_tsub_left hp 1) r)

/-- A finite target family, with no independence asserted between targets. -/
theorem finite_seed_failure (a : I) (seed : Finset (List Bool)) (L : ℕ)
    (hseed : ∀ v ∈ seed, 0 < v.length ∧ v.length ≤ L) (r : ℕ) :
    infiniteSplitPi a {ω |
      (∃ w, recordCap L r < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w) ∧
      ¬ ∀ v ∈ seed, FiniteReversibleGenerated (recordCap L r) 2 (currySplitField ω) v} ≤
      (seed.card : ENNReal) * (1-(toNNReal a : ENNReal)^(L+1))^r := by
  have hsub : {ω : SplitField |
      (∃ w, recordCap L r < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w) ∧
      ¬ ∀ v ∈ seed, FiniteReversibleGenerated (recordCap L r) 2 (currySplitField ω) v} ⊆
      ⋃ v ∈ seed, escapedMissing (recordCap L r) v := by
    intro ω hω
    push Not at hω
    obtain ⟨v,hv,hmissing⟩ := hω.2
    exact Set.mem_iUnion.mpr ⟨v,Set.mem_iUnion.mpr ⟨hv,hω.1,hmissing⟩⟩
  calc
    _ ≤ infiniteSplitPi a (⋃ v ∈ seed, escapedMissing (recordCap L r) v) := measure_mono hsub
    _ ≤ ∑ v ∈ seed, infiniteSplitPi a (escapedMissing (recordCap L r) v) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _v ∈ seed, (1-(toNNReal a : ENNReal)^(L+1))^r := by
      apply Finset.sum_le_sum
      intro v hv
      exact common_cap_target_failure a v (hseed v hv).1 L (hseed v hv).2 r
    _ = _ := by simp

end RAFCriticalWindowQuantitative
