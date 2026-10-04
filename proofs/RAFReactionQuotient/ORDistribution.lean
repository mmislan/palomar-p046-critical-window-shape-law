module

public import proofs.RAFReactionQuotient.ORLaw

@[expose] public section

namespace RAFReactionQuotient
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold

theorem probability_prop_eq_of_false (μ ν : Measure Prop)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : μ {False} = ν {False}) : μ = ν := by
  apply Measure.ext_of_singleton
  intro q
  by_cases hq : q
  · have he : q = True := propext (iff_true_intro hq)
    have hs : ({True} : Set Prop) = {False}ᶜ := by ext t; simp
    rw [he,hs,measure_compl (MeasurableSet.singleton _) (measure_ne_top _ _),
      measure_compl (MeasurableSet.singleton _) (measure_ne_top _ _),measure_univ,measure_univ,h]
  · have he : q = False := propext (iff_false_intro hq)
    simpa only [he] using h

variable {R J : Type*} [Fintype R]

noncomputable def fibreParameter (π : R → J) (p : I) (j : J) : I :=
  σ ((σ p) ^ (Finset.univ.filter (fun r => π r = j)).card)

theorem fibreParameter_value (π : R → J) (p : I) (j : J) :
    (fibreParameter π p j : ℝ) =
      1-(1-(p : ℝ))^(Finset.univ.filter (fun r => π r = j)).card := by
  simp [fibreParameter]

theorem fieldOR_marginal (π : R → J) (p : I) (j : J) :
    (RAFEmergenceApprox.Generic.colLaw R p).map (fun ω => fieldOR π ω j) =
      ambientCoordLaw (fibreParameter π p j) := by
  have hm := measurable_of_finite (fun ω : R → Prop => fieldOR π ω j)
  apply probability_prop_eq_of_false
  rw [Measure.map_apply hm (MeasurableSet.singleton _)]
  have he : (fun ω : R → Prop => fieldOR π ω j) ⁻¹' {False} =
      {ω | ¬ fieldOR π ω j} := by ext ω; simp
  rw [he,fieldOR_closed_probability,ambientCoordLaw_false]
  simp only [fibreParameter, symm_symm]
  rw [← ENNReal.coe_pow]
  congr 1

/-- The complete quotient ensemble is a product law with its actual fibre
probabilities. Singleton and double fibres need not have the same parameter. -/
theorem fieldOR_map [Fintype J] (π : R → J) (p : I) :
    (RAFEmergenceApprox.Generic.colLaw R p).map (fieldOR π) =
      Measure.pi (fun j => ambientCoordLaw (fibreParameter π p j)) := by
  have he := (fieldOR_independent π p).map_fun_eq_pi_map
    (fun _ => (measurable_of_finite _).aemeasurable)
  change (RAFEmergenceApprox.Generic.colLaw R p).map (fieldOR π) = _ at he
  rw [he]
  congr 1
  funext j
  exact fieldOR_marginal π p j

end RAFReactionQuotient
