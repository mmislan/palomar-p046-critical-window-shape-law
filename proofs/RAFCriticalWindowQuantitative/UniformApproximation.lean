module

public import proofs.RAFCriticalWindowQuantitative.CertifiedEvaluator
public import proofs.RAFCriticalWindowQuantitative.QuotientCertifiedEvaluator

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval

theorem uniform_record_budget (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (L : ℕ)
    (ε : ℚ) (hε : 0 < ε) (a : I) (ha : rationalParameter q hq.le hq1 ≤ a) :
    ((actualBinaryWords L).card : ℝ) * (1-(a : ℝ)^(L+1))^(recordIndex q hq hq1 L ε hε) ≤
      (ε : ℝ)/4 := by
  have hq0 : (0 : ℝ) ≤ q := by exact_mod_cast hq.le
  have hqa : (q : ℝ) ≤ a := ha
  have hpow := pow_le_pow_left₀ hq0 hqa (L+1)
  have hnonneg : (0 : ℝ) ≤ 1-(a : ℝ)^(L+1) :=
    sub_nonneg.mpr (pow_le_one₀ a.property.1 a.property.2)
  exact (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hnonneg (sub_le_sub_left hpow 1) _) (Nat.cast_nonneg _)).trans
    (real_record_budget q hq hq1 L ε hε)

theorem split_uniform_approximation (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (ε : ℚ) (hε : 0 < ε) (a : I) (ha : rationalParameter q hq.le hq1 ≤ a) :
    (splitEscapeProbability a (splitEvaluationCap q hq hq1 ε hε)).toReal ≤
      (staticSurvival a).toReal + (ε : ℝ)/2 := by
  let m := precisionIndex ε
  let L := 10*seedIndex q hq hq1 m
  let r := recordIndex q hq hq1 L ε hε
  have hm : 2 ≤ m := precisionIndex_ge_two ε
  have hS : staticSurvival a ≠ ⊤ := by unfold staticSurvival; exact measure_ne_top _ _
  have ht := real_error_of_bound _ _ hS m L r (by omega) a
    (explicit_split_truncation q hq hq1 m hm a ha r)
  have hp : 1/(m : ℝ) ≤ (ε : ℝ)/4 := by
    have hcast := (Rat.cast_le (K := ℝ)).mpr (precisionIndex_error ε hε)
    push_cast at hcast
    exact hcast
  have hr := uniform_record_budget q hq hq1 L ε hε a ha
  change (splitEscapeProbability a (recordCap L r)).toReal ≤ _
  linarith

theorem quotient_uniform_approximation (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (ε : ℚ) (hε : 0 < ε) (a : I) (ha : rationalParameter q hq.le hq1 ≤ a) :
    (quotientEscapeProbability a (quotientEvaluationCap q hq hq1 ε hε)).toReal ≤
      (quotientSurvival a).toReal + (ε : ℝ)/2 := by
  let m := precisionIndex ε
  have hh : 0 < q/2 := by positivity
  have hh1 : q/2 ≤ 1 := by linarith
  let L := 10*seedIndex (q/2) hh hh1 m
  let r := recordIndex q hq hq1 L ε hε
  have hm : 2 ≤ m := precisionIndex_ge_two ε
  have hS : quotientSurvival a ≠ ⊤ := by unfold quotientSurvival; exact measure_ne_top _ _
  have ht := real_error_of_bound _ _ hS m L r (by omega) a
    (explicit_quotient_truncation q hq hq1 m hm a ha r)
  have hp : 1/(m : ℝ) ≤ (ε : ℝ)/4 := by
    have hcast := (Rat.cast_le (K := ℝ)).mpr (precisionIndex_error ε hε)
    push_cast at hcast
    exact hcast
  have hr := uniform_record_budget q hq hq1 L ε hε a ha
  change (quotientEscapeProbability a (recordCap L r)).toReal ≤ _
  linarith

end RAFCriticalWindowQuantitative
