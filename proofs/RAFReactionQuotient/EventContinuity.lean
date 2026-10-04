module

public import proofs.RAFReactionQuotient.SeedBulk
public import proofs.HordijkSteelThreshold.StaticEventContinuity

@[expose] public section

namespace RAFReactionQuotient
open Classical MeasureTheory unitInterval HordijkSteelThreshold OverlapCorrectedRAF.Source
open scoped ENNReal

theorem quotientStaticMeasure_atom (N : ℕ) (a : I) (ω : RepositoryChannel N → Prop) :
    quotientStaticMeasure N a {ω} = (∏ r, staticAtomWeight a (ω r) : NNReal) := by
  rw [quotientStaticMeasure,Measure.pi_singleton]
  simp only [ambientCoordLaw_atom,ENNReal.ofNNReal_finsetProd]

theorem continuous_quotient_event_probability (N : ℕ) (E : Set (RepositoryChannel N → Prop)) :
    Continuous (fun a : I => quotientStaticMeasure N a E) := by
  let F : Finset (RepositoryChannel N → Prop) := Finset.univ.filter (fun ω => ω ∈ E)
  have he (a : I) : quotientStaticMeasure N a E =
      ((∑ ω ∈ F, ∏ r, staticAtomWeight a (ω r) : NNReal) : ENNReal) := by
    have hF : (F : Set (RepositoryChannel N → Prop)) = E := by ext ω; simp [F]
    rw [← hF,← sum_measure_singleton]
    simp only [quotientStaticMeasure_atom,ENNReal.ofNNReal_finsetSum]
  simp_rw [he]
  apply ENNReal.continuous_coe.comp
  apply continuous_finsetSum
  intro ω _
  apply continuous_finsetProd
  intro r _
  exact continuous_staticAtomWeight (ω r)

end RAFReactionQuotient
