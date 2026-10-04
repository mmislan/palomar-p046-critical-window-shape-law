module

public import proofs.RAFReactionQuotient.SeedApproximation
public import proofs.RAFReactionQuotient.EventContinuity

@[expose] public section

namespace RAFReactionQuotient
open Classical Filter MeasureTheory RAF.Polymer RAF.Concrete unitInterval HordijkSteelThreshold
open scoped ENNReal Topology

theorem quotientSurvival_le_finite_escape (a : I) (K : ℕ) :
    quotientSurvival a ≤ quotientStaticMeasure (2*(K+2)) a (quotientEscapeEvent 2 K) := by
  rw [quotient_escape_measure_eq, quotientSurvival_eq]
  apply measure_mono
  intro field hf
  exact (reversibleEscapeEvent_iff 2 K field).mpr (hf (K+2))

/-- Sequential continuity at every positive openness, with no uniform finite
witness cap assumed. -/
theorem quotientSurvival_tendsto {u : ℕ → I} {a : I}
    (ha : 0 < (a : ℝ)) (hu : Tendsto u atTop (𝓝 a)) :
    Tendsto (fun n => quotientSurvival (u n)) atTop (𝓝 (quotientSurvival a)) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    obtain ⟨d,hcd,hds⟩ := exists_between hc
    have ht : Tendsto (fun m : ℕ => c+(m : ENNReal)⁻¹) atTop (𝓝 c) := by
      simpa using (tendsto_const_nhds.add ENNReal.tendsto_inv_nat_nhds_zero :
        Tendsto (fun m : ℕ => c+(m : ENNReal)⁻¹) atTop (𝓝 (c+0)))
    obtain ⟨m,hem,hm⟩ := ((ht.eventually_lt_const hcd).and (eventually_ge_atTop 2)).exists
    let b0 : I := ⟨(a : ℝ)/2, by constructor <;> nlinarith [a.property.1,a.property.2]⟩
    have hb0 : 0 < (b0 : ℝ) := by dsimp [b0]; positivity
    obtain ⟨L,_hL,hseed⟩ := quotient_seed_le_survival_error b0 hb0 m hm
    have hg := quotientSurvival_le_seed a ha (actualBinaryWords L)
      (fun w hw => List.length_pos_iff.mpr ((mem_actualBinaryWords w L).mp hw).1)
    obtain ⟨N,hN⟩ := ((quotient_finite_seed_tendsto 2 a (actualBinaryWords L)).eventually_const_lt
      (hds.trans_le hg)).exists
    have hfinite := ((continuous_quotient_event_probability N
      {ω | ∀ w ∈ actualBinaryWords L, ∃ x ∈ quotientClosure N 2
        (quotientOpen ω), moleculeWord x = w}).tendsto a).comp hu
    have hbase : ∀ᶠ n in atTop, b0 ≤ u n := by
      have hr := continuous_subtype_val.continuousAt.tendsto.comp hu
      exact (hr.eventually_const_lt (show (b0 : ℝ) < (a : ℝ) by dsimp [b0]; linarith)).mono
        (fun _ h => h.le)
    filter_upwards [hfinite.eventually_const_lt hN,hbase] with n hn hbn
    have hf : quotientStaticMeasure N (u n) {ω | ∀ w ∈ actualBinaryWords L,
        ∃ x ∈ quotientClosure N 2 (quotientOpen ω), moleculeWord x = w} ≤
        quotientInfiniteMeasure (u n) {field | ∀ w ∈ actualBinaryWords L,
          InfiniteReversibleGenerated 2 field w} := by
      rw [quotient_finite_seed_measure_eq]
      apply measure_mono
      intro field h w hw
      exact finiteReversibleGenerated_to_infinite (h w hw)
    exact lt_of_add_lt_add_right (hem.trans (hn.trans_le (hf.trans (hseed (u n) hbn))))
  · intro c hc
    obtain ⟨K,hK⟩ := ((quotient_escape_tendsto a).eventually_lt_const hc).exists
    have ht := ((continuous_quotient_event_probability (2*(K+2)) (quotientEscapeEvent 2 K)).tendsto a).comp hu
    exact (ht.eventually_lt_const hK).mono (fun n hn => (quotientSurvival_le_finite_escape (u n) K).trans_lt hn)

end RAFReactionQuotient
