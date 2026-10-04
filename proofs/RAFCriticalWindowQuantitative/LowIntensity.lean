module

public import proofs.RAFCriticalWindowQuantitative.SmallOpenness
public import proofs.RAFReactionQuotient.Resolution

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient unitInterval

theorem criticalOpenness_pos_le (lam : ℝ) (hlam : 0 < lam) :
    0 < (criticalOpenness lam hlam : ℝ) ∧ (criticalOpenness lam hlam : ℝ) ≤ lam := by
  change 0 < 1-Real.exp (-lam) ∧ 1-Real.exp (-lam) ≤ lam
  constructor
  · have h := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hlam)
    linarith
  · linarith [Real.add_one_le_exp (-lam)]

theorem power_bound_intensity_flatness (S : I → ℝ) (C : ℕ → ℕ)
    (hbound : ∀ a r, S a ≤ (C r : ℝ)*(a : ℝ)^r) (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ lam : ℝ, ∀ hlam : 0 < lam, lam < δ →
      S (criticalOpenness lam hlam) < ε*lam^d := by
  obtain ⟨δ,hδ,h⟩ := power_bound_implies_flatness S C hbound d ε hε
  refine ⟨δ,hδ,?_⟩
  intro lam hlam hlamδ
  have ha := criticalOpenness_pos_le lam hlam
  exact (h _ ha.1 (ha.2.trans_lt hlamδ)).trans_le
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.1.le ha.2 d) hε.le)

theorem conditional_power_bound (S : I → ℝ) (C : ℕ → ℕ)
    (hbound : ∀ a r, S a ≤ (C r : ℝ)*(a : ℝ)^r)
    (g : ℕ) (hg : 0 < g) (a : I) (ha : 0 < (a : ℝ)) (r : ℕ) :
    S a/(1-(1-(a : ℝ))^g) ≤ (C (r+1) : ℝ)*(a : ℝ)^r := by
  have hden : (a : ℝ) ≤ 1-(1-(a : ℝ))^g := by
    have h := pow_le_pow_of_le_one (sub_nonneg.mpr a.property.2)
      (show 1-(a : ℝ) ≤ 1 by linarith [a.property.1]) (show 1 ≤ g by omega)
    simp only [pow_one] at h
    linarith
  apply (div_le_iff₀ (ha.trans_le hden)).mpr
  calc
    S a ≤ (C (r+1) : ℝ)*(a : ℝ)^(r+1) := hbound a (r+1)
    _ = ((C (r+1) : ℝ)*(a : ℝ)^r)*(a : ℝ) := by rw [pow_succ,mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)

theorem split_low_intensity_flatness (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ lam : ℝ, ∀ hlam : 0 < lam, lam < δ →
      (staticSurvival (criticalOpenness lam hlam)).toReal < ε*lam^d :=
  power_bound_intensity_flatness _ splitSparseCoefficient split_sparse_real d ε hε

theorem quotient_low_intensity_flatness (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ lam : ℝ, ∀ hlam : 0 < lam, lam < δ →
      quotientTransitionLimit lam hlam < ε*lam^d :=
  power_bound_intensity_flatness _ quotientSparseCoefficient quotient_sparse_real d ε hε

theorem conditional_intensity_flatness (S : I → ℝ) (C : ℕ → ℕ)
    (hbound : ∀ a r, S a ≤ (C r : ℝ)*(a : ℝ)^r) (g : ℕ) (hg : 0 < g)
    (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ lam : ℝ, ∀ hlam : 0 < lam, lam < δ →
      S (criticalOpenness lam hlam)/(1-(1-(criticalOpenness lam hlam : ℝ))^g) < ε*lam^d := by
  apply power_bound_intensity_flatness (fun a => S a/(1-(1-(a : ℝ))^g)) (fun r => C (r+1)) _ d ε hε
  intro a r
  by_cases ha : 0 < (a : ℝ)
  · exact conditional_power_bound S C hbound g hg a ha r
  · have he : (a : ℝ) = 0 := by linarith [a.property.1]
    simp only [he,sub_zero,one_pow,sub_self,div_zero]
    positivity

theorem split_conditional_intensity_flatness (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ lam : ℝ, ∀ hlam : 0 < lam, lam < δ →
      (staticSurvival (criticalOpenness lam hlam)).toReal /
        (1-(1-(criticalOpenness lam hlam : ℝ))^36) < ε*lam^d :=
  conditional_intensity_flatness _ splitSparseCoefficient split_sparse_real 36 (by omega) d ε hε

theorem quotient_conditional_intensity_flatness (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ lam : ℝ, ∀ hlam : 0 < lam, lam < δ →
      quotientTransitionLimit lam hlam /
        (1-(1-(criticalOpenness lam hlam : ℝ))^34) < ε*lam^d :=
  conditional_intensity_flatness _ quotientSparseCoefficient quotient_sparse_real 34 (by omega) d ε hε

end RAFCriticalWindowQuantitative
