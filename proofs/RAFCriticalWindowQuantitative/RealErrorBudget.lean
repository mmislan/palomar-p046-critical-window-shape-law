module

public import proofs.RAFCriticalWindowQuantitative.ApproximationParameters
public import proofs.RAFCriticalWindowQuantitative.FiniteEscapeAdapters

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold MeasureTheory unitInterval
open scoped ENNReal

theorem real_record_budget (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (L : ℕ)
    (ε : ℚ) (hε : 0 < ε) :
    ((actualBinaryWords L).card : ℝ) * (1-(q : ℝ)^(L+1))^(recordIndex q hq hq1 L ε hε) ≤
      (ε : ℝ)/4 := by
  have h := (recordIndex_error q hq hq1 L ε hε).2
  have hr := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at hr
  have hc : (actualBinaryWords L).card ≤ 2^(L+1) := by
    rw [actualBinaryWords_card]
    exact Nat.sub_le _ _
  have hcR : ((actualBinaryWords L).card : ℝ) ≤ (2 : ℝ)^(L+1) := by exact_mod_cast hc
  have ht : (0 : ℝ) ≤ 1-(q : ℝ)^(L+1) := by
    exact_mod_cast (repair_ratio q hq hq1 L).1
  exact (mul_le_mul_of_nonneg_right hcR (pow_nonneg ht _)).trans hr

theorem real_error_of_bound (e S : ENNReal) (hS : S ≠ ∞) (m L r : ℕ) (hm : 0 < m)
    (a : I) (h : e ≤ S+(m : ENNReal)⁻¹+
      ((actualBinaryWords L).card : ENNReal)*(1-(toNNReal a : ENNReal)^(L+1))^r) :
    e.toReal ≤ S.toReal+1/(m : ℝ)+
      ((actualBinaryWords L).card : ℝ)*(1-(a : ℝ)^(L+1))^r := by
  have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hp : (toNNReal a : ENNReal)^(L+1) ≤ 1 :=
    pow_le_one₀ (by positivity) (by exact_mod_cast a.property.2)
  have ht : ((actualBinaryWords L).card : ENNReal)*(1-(toNNReal a : ENNReal)^(L+1))^r ≠ ∞ := by
    finiteness
  have hi : (m : ENNReal)⁻¹ ≠ ∞ := by simp [hm0]
  have hsum : S+(m : ENNReal)⁻¹ ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hS,hi⟩
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hsum,ht⟩) h
  rw [ENNReal.toReal_add hsum ht, ENNReal.toReal_add hS hi,
    ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_sub_of_le hp (by simp)] at hr
  simpa [one_div] using hr

end RAFCriticalWindowQuantitative
