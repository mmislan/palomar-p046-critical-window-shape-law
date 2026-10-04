module

public import proofs.RAFCriticalWindowQuantitative.ExplicitTruncation
public import proofs.RAFCriticalWindowQuantitative.QuotientExplicitTruncation
public import proofs.HordijkSteelThreshold.StaticSurvivalContinuity

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval RAF.Polymer
open scoped ENNReal

theorem split_escape_finite (a : I) (K : ℕ) (hK : 2 ≤ K) :
    splitEscapeProbability a K =
      staticReactionMeasure (2*((K-2)+2)) a (staticEscapeEvent 2 (K-2)) := by
  unfold splitEscapeProbability
  rw [finite_static_escape_measure_eq, infiniteStaticMeasure,
    Measure.map_apply measurable_currySplitField (measurableSet_reversibleEscapeEvent 2 (K-2))]
  congr 1
  ext ω
  change (∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w) ↔ _
  rw [Set.mem_preimage, reversibleEscapeEvent_iff]
  have he : K-2+2 = K := by omega
  rw [he]

theorem split_survival_le_escape (a : I) (K : ℕ) : staticSurvival a ≤ splitEscapeProbability a K := by
  rw [staticSurvival, infiniteStaticMeasure,
    Measure.map_apply measurable_currySplitField (measurableSet_reversibleUnbounded 2)]
  apply measure_mono
  intro ω hω
  exact hω K

theorem quotient_escape_finite (a : I) (K : ℕ) (hK : 2 ≤ K) :
    quotientEscapeProbability a K =
      quotientStaticMeasure (2*((K-2)+2)) a (quotientEscapeEvent 2 (K-2)) := by
  unfold quotientEscapeProbability
  rw [quotient_escape_measure_eq, quotientInfiniteMeasure,
    Measure.map_apply quotientField_measurable (measurableSet_reversibleEscapeEvent 2 (K-2))]
  congr 1
  ext ω
  change (∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (quotientField ω) w) ↔ _
  rw [Set.mem_preimage, reversibleEscapeEvent_iff]
  have he : K-2+2 = K := by omega
  rw [he]

theorem quotient_survival_le_escape (a : I) (K : ℕ) :
    quotientSurvival a ≤ quotientEscapeProbability a K := by
  apply measure_mono
  intro ω hω
  exact hω K

end RAFCriticalWindowQuantitative
