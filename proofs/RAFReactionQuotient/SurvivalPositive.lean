module

public import proofs.RAFReactionQuotient.FiniteApproximation
public import proofs.HordijkSteelThreshold.TransitionConsequences

@[expose] public section

set_option Elab.async false

namespace RAFReactionQuotient
open Classical Filter MeasureTheory unitInterval HordijkSteelThreshold
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open scoped ENNReal Topology

theorem split_half_survival_le_quotient (a : I) : staticSurvival (halfParameter a) ≤ quotientSurvival a := by
  have hK (K : ℕ) :
      staticReactionMeasure (2*(K+2)) (halfParameter a) (staticEscapeEvent 2 K) ≤
      quotientStaticMeasure (2*(K+2)) a (quotientEscapeEvent 2 K) := by
    let n := 2*(K+2)
    have h := OR_half_domination (@splitToQuotient n) a
      (fun j => by
        convert split_fibre_le_two j using 1
        congr 1
        ext r
        simp)
      (fun q => ∃ x ∈ quotientClosure n 2 (quotientOpen q), K+2 < (moleculeWord x).length) (by
        intro q r hqr hq
        obtain ⟨x,hx,hl⟩ := hq
        refine ⟨x,quotientClosure_mono n 2 ?_ hx,hl⟩
        intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hqr j (Finset.mem_filter.mp hj).2⟩)
    simp only [quotientClosure_OR] at h
    simpa only [staticReactionMeasure,Measure.infinitePi_eq_pi,
      RAFEmergenceApprox.Generic.colLaw,staticEscapeEvent,quotientEscapeEvent,quotientStaticMeasure] using h
  exact le_of_tendsto_of_tendsto' (finite_static_escape_probability_tendsto (halfParameter a))
    (quotient_escape_tendsto a) hK

theorem quotientSurvival_pos (a : I) (ha : 0 < (a : ℝ)) : 0 < quotientSurvival a :=
  (staticSurvival_pos (halfParameter a) (by change 0 < (a : ℝ)/2; positivity)).trans_le
    (split_half_survival_le_quotient a)

end RAFReactionQuotient
