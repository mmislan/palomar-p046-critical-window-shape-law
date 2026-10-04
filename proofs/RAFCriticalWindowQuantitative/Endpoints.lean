module

public import proofs.RAFCriticalWindowQuantitative.SmallOpenness
public import proofs.RAFCriticalWindowQuantitative.CertifiedEvaluator
public import proofs.RAFCriticalWindowQuantitative.QuotientCertifiedEvaluator

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient unitInterval

theorem split_survival_zero : staticSurvival 0 = 0 := by
  apply le_antisymm _ (by positivity)
  simpa only [toNNReal_zero,ENNReal.coe_zero,zero_pow Nat.one_ne_zero,mul_zero] using split_sparse_probability 0 1

theorem quotient_survival_zero : quotientSurvival 0 = 0 := by
  apply le_antisymm _ (by positivity)
  simpa only [toNNReal_zero,ENNReal.coe_zero,zero_pow Nat.one_ne_zero,mul_zero] using quotient_sparse_probability 0 1

def splitTotalInterval (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℚ × ℚ :=
  if h : q = 0 then (0,0) else splitCertifiedInterval q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε

def quotientTotalInterval (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℚ × ℚ :=
  if h : q = 0 then (0,0) else quotientCertifiedInterval q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε

theorem splitTotalInterval_correct (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) :
    let v := splitTotalInterval q hq hq1 ε hε
    (v.1 : ℝ) ≤ (staticSurvival (rationalParameter q hq hq1)).toReal ∧
      (staticSurvival (rationalParameter q hq hq1)).toReal ≤ (v.2 : ℝ) ∧ v.2-v.1 < ε := by
  by_cases h : q = 0
  · subst q
    have he : rationalParameter 0 hq hq1 = 0 := by apply Subtype.ext; simp [rationalParameter]
    simp [splitTotalInterval,he,split_survival_zero,hε]
  · simpa only [splitTotalInterval,dite_eq_right h] using
      splitCertifiedInterval_correct q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε

theorem quotientTotalInterval_correct (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) :
    let v := quotientTotalInterval q hq hq1 ε hε
    (v.1 : ℝ) ≤ (quotientSurvival (rationalParameter q hq hq1)).toReal ∧
      (quotientSurvival (rationalParameter q hq hq1)).toReal ≤ (v.2 : ℝ) ∧ v.2-v.1 < ε := by
  by_cases h : q = 0
  · subst q
    have he : rationalParameter 0 hq hq1 = 0 := by apply Subtype.ext; simp [rationalParameter]
    simp [quotientTotalInterval,he,quotient_survival_zero,hε]
  · simpa only [quotientTotalInterval,dite_eq_right h] using
      quotientCertifiedInterval_correct q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε

end RAFCriticalWindowQuantitative
