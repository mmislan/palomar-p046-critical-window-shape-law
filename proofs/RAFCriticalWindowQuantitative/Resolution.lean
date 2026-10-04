module

public import proofs.RAFCriticalWindowQuantitative.SourceCalibration
public import proofs.RAFCriticalWindowQuantitative.UniformApproximation
public import proofs.RAFCriticalWindowQuantitative.LowIntensity
public import proofs.RAFCriticalWindowQuantitative.ProductiveHistory
public import proofs.RAFCriticalWindowQuantitative.WorkedBound

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient unitInterval RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

/-- Quantitative properties of the specified actual profile and executable programs. -/
structure ProfileGuarantees (S : I → ENNReal) (escape : I → ℕ → ENNReal)
    (evaluate : (q : ℚ) → 0 ≤ q → q ≤ 1 → (ε : ℚ) → 0 < ε → ℚ × ℚ)
    (cap : (q : ℚ) → 0 < q → q ≤ 1 → (ε : ℚ) → 0 < ε → ℕ)
    (coefficient : ℕ → ℕ) : Prop where
  enclosure : ∀ q hq hq1 ε hε,
    let v := evaluate q hq hq1 ε hε
    (v.1 : ℝ) ≤ (S (rationalParameter q hq hq1)).toReal ∧
      (S (rationalParameter q hq hq1)).toReal ≤ (v.2 : ℝ) ∧ v.2-v.1 < ε
  uniform_error : ∀ q hq hq1 ε hε a, rationalParameter q (le_of_lt hq) hq1 ≤ a →
    (escape a (cap q hq hq1 ε hε)).toReal ≤ (S a).toReal+(ε : ℝ)/2
  power_bound : ∀ a r, (S a).toReal ≤ (coefficient r : ℝ)*(a : ℝ)^r
  intensity_flatness : ∀ d ε, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ lam : ℝ, ∀ hlam : 0 < lam, lam < δ → (S (criticalOpenness lam hlam)).toReal < ε*lam^d

theorem split_profile_guarantees : ProfileGuarantees staticSurvival splitEscapeProbability
    splitTotalInterval splitEvaluationCap splitSparseCoefficient :=
  ⟨splitTotalInterval_correct,split_uniform_approximation,split_sparse_real,split_low_intensity_flatness⟩

theorem quotient_profile_guarantees : ProfileGuarantees quotientSurvival quotientEscapeProbability
    quotientTotalInterval quotientEvaluationCap quotientSparseCoefficient :=
  ⟨quotientTotalInterval_correct,quotient_uniform_approximation,quotient_sparse_real,quotient_low_intensity_flatness⟩

/-- The source contract uses actual catalytic inputs, not an assumed convergence rate. -/
def SourceGuarantees : Prop :=
  (∀ n m K, ∀ _hn : 4 ≤ n, ∀ _hm : 0 < m,
    ∀ p hp hp1 q hq hq1, ∀ _hk : 6 < nearFullPoolSize n m,
    ∀ _hpool : q ≤ rationalPool p (nearFullPoolSize n m),
    ∀ s hs hs1 ε hε,
    |(splitCatalyticProbability n (rationalParameter p hp hp1)).toReal -
      (staticSurvival (rationalParameter s hs hs1)).toReal| ≤
      (rationalIntervalError (splitSourceInterval n m K p q hq hq1)
        (splitTotalInterval s hs hs1 ε hε) : ℝ)) ∧
  (∀ n m K, ∀ _hn : 0 < n, ∀ _hm : 0 < m,
    ∀ p hp hp1 q hq hq1, ∀ _hk : 6 < nearFullPoolSize n m,
    ∀ _hpool : q ≤ rationalPool p (nearFullPoolSize n m),
    ∀ s hs hs1 ε hε,
    |(quotientRAFProbability n (rationalParameter p hp hp1)).toReal -
      (quotientSurvival (rationalParameter s hs hs1)).toReal| ≤
      (rationalIntervalError (quotientSourceInterval n m K p q hq hq1)
        (quotientTotalInterval s hs hs1 ε hε) : ℝ))

theorem finite_source_guarantees : SourceGuarantees :=
  ⟨split_source_profile_error,quotient_source_profile_error⟩

/-- Compiled minimum quantitative/computability successor for both literal RAF models.
The programs are explicit definitions; no desired bound or validity oracle is assumed. -/
theorem quantitative_critical_window_resolution :
    ProfileGuarantees staticSurvival splitEscapeProbability
      splitTotalInterval splitEvaluationCap splitSparseCoefficient ∧
    ProfileGuarantees quotientSurvival quotientEscapeProbability
      quotientTotalInterval quotientEvaluationCap quotientSparseCoefficient ∧
    SourceGuarantees ∧
    (∀ N k S x, x ∈ temporaryReactionClosure (N := N) 2 S → 2^(k+1) < molLength x →
      ∃ T, ProductiveHistory (binaryPolymerCRS N 2) S k T ∧ T.card = k ∧ T ⊆ S) ∧
    (∀ N k S x, x ∈ quotientClosure N 2 S → 2^(k+1) < molLength x →
      ∃ T, ProductiveHistory (repositoryCRS N 2) S k T ∧ T.card = k ∧ T ⊆ S) ∧
    (∀ a : I, (a : ℝ) ≤ 1/10^20 → (staticSurvival a).toReal < 8/10^26) :=
  ⟨split_profile_guarantees,quotient_profile_guarantees,finite_source_guarantees,
    split_long_target_history,quotient_long_target_history,worked_low_openness_bound⟩

end RAFCriticalWindowQuantitative
