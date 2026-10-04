module

public import proofs.RAFReactionQuotient.InfiniteDock
public import proofs.RAFReactionQuotient.Richness

@[expose] public section

namespace RAFReactionQuotient
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

noncomputable def quotientInfiniteMeasure (a : I) : Measure InfiniteSplitEnvironment :=
  (infiniteSplitPi a).map quotientField

noncomputable instance quotientInfinite_probability (a : I) :
    IsProbabilityMeasure (quotientInfiniteMeasure a) := by
  unfold quotientInfiniteMeasure
  infer_instance

theorem quotientSurvival_eq (a : I) : quotientSurvival a =
    quotientInfiniteMeasure a {field | ReversibleUnbounded 2 field} := by
  rw [quotientInfiniteMeasure,Measure.map_apply quotientField_measurable
    (measurableSet_reversibleUnbounded 2)]
  rfl

theorem quotientClosure_pullback {n L : ℕ} (q : RepositoryChannel n → Prop) :
    quotientClosure n L (quotientOpen q) =
      temporaryReactionClosure L (staticOpenReactions (fun r => q (splitToQuotient r))) := by
  have he : fieldOR splitToQuotient (fun r => q (splitToQuotient r)) = q := by
    funext j
    exact propext (quotient_mark_pullback_OR q j)
  rw [← quotientClosure_OR,he]

theorem quotientClosure_restriction (n L : ℕ) (ω : SplitField) :
    quotientClosure n L (quotientOpen (fun j => ω (quotientCoordinate j))) =
      temporaryReactionClosure L (restrictedSplitReactions n (quotientField ω)) := by
  rw [quotientClosure_pullback]
  congr 1
  ext r
  simp only [staticOpenReactions,restrictedSplitReactions,Finset.mem_filter,Finset.mem_univ,
    true_and]
  unfold quotientField
  apply Iff.of_eq
  simpa only [literalSplitCoordinate] using congrArg ω (canonicalIndex_split r).symm

theorem quotient_finite_seed_measure_eq (n L : ℕ) (a : I) (seed : Finset (List Bool)) :
    quotientStaticMeasure n a {q | ∀ w ∈ seed,
      ∃ x ∈ quotientClosure n L (quotientOpen q), moleculeWord x = w} =
    quotientInfiniteMeasure a {field | ∀ w ∈ seed, FiniteReversibleGenerated n L field w} := by
  rw [← infinite_quotient_restriction_map n a,
    Measure.map_apply (Measurable.of_eval (fun j => measurable_pi_apply _))
      (Set.toFinite _).measurableSet,
    quotientInfiniteMeasure,Measure.map_apply quotientField_measurable
      (measurableSet_finite_seed n L seed)]
  congr 1
  ext ω
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,quotientClosure_restriction]
  apply forall_congr'
  intro w
  apply forall_congr'
  intro _
  exact (finiteReversible_iff_literalClosure (quotientField ω) w).symm

theorem quotient_finite_seed_tendsto (L : ℕ) (a : I) (seed : Finset (List Bool)) :
    Filter.Tendsto (fun n => quotientStaticMeasure n a {q | ∀ w ∈ seed,
      ∃ x ∈ quotientClosure n L (quotientOpen q), moleculeWord x = w}) Filter.atTop
      (nhds (quotientInfiniteMeasure a {field | ∀ w ∈ seed, InfiniteReversibleGenerated L field w})) := by
  simp_rw [quotient_finite_seed_measure_eq]
  exact finite_seed_probability_tendsto (quotientInfiniteMeasure a) L seed

theorem quotient_target_ae (a : I) (ha : 0 < (a : ℝ)) (v : List Bool) (hv : 0 < v.length) :
    ∀ᵐ field ∂quotientInfiniteMeasure a, ReversibleUnbounded 2 field →
      InfiniteReversibleGenerated 2 field v := by
  rw [ae_iff]
  have he : {field : InfiniteSplitEnvironment | ¬ (ReversibleUnbounded 2 field →
      InfiniteReversibleGenerated 2 field v)} =
      {field | ReversibleUnbounded 2 field} ∩
        {field | InfiniteReversibleGenerated 2 field v}ᶜ := by ext field; simp
  rw [he,quotientInfiniteMeasure,Measure.map_apply quotientField_measurable
    ((measurableSet_reversibleUnbounded 2).inter
      (measurableSet_infiniteReversibleGenerated 2 v).compl)]
  exact quotient_missing_target_null a ha v hv

theorem quotientSurvival_le_seed (a : I) (ha : 0 < (a : ℝ))
    (seed : Finset (List Bool)) (hseed : ∀ w ∈ seed, 0 < w.length) :
    quotientSurvival a ≤ quotientInfiniteMeasure a
      {field | ∀ w ∈ seed, InfiniteReversibleGenerated 2 field w} := by
  rw [quotientSurvival_eq]
  apply measure_mono_ae
  have hall : ∀ᵐ field ∂quotientInfiniteMeasure a, ∀ w : seed,
      ReversibleUnbounded 2 field → InfiniteReversibleGenerated 2 field w.val :=
    (ae_all_iff).mpr (fun w => quotient_target_ae a ha w.val (hseed w.val w.property))
  filter_upwards [hall] with field hfield
  intro hu w hw
  exact hfield ⟨w,hw⟩ hu

def quotientEscapeEvent (L K : ℕ) : Set (RepositoryChannel (2*(K+L)) → Prop) :=
  {q | ∃ x ∈ quotientClosure (2*(K+L)) L (quotientOpen q), K+L < (moleculeWord x).length}

theorem quotient_escape_measure_eq (L K : ℕ) (a : I) :
    quotientStaticMeasure (2*(K+L)) a (quotientEscapeEvent L K) =
      quotientInfiniteMeasure a (reversibleEscapeEvent L K) := by
  rw [← infinite_quotient_restriction_map (2*(K+L)) a,
    Measure.map_apply (Measurable.of_eval (fun j => measurable_pi_apply _))
      (Set.toFinite _).measurableSet,
    quotientInfiniteMeasure,Measure.map_apply quotientField_measurable
      (measurableSet_reversibleEscapeEvent L K)]
  congr 1
  ext ω
  change (∃ x ∈ quotientClosure _ L (quotientOpen (fun j => ω (quotientCoordinate j))),
    K+L < (moleculeWord x).length) ↔
    ∃ w, K+L < w.length ∧ FiniteReversibleGenerated (2*(K+L)) L (quotientField ω) w
  rw [quotientClosure_restriction]
  constructor
  · rintro ⟨x,hx,hl⟩
    exact ⟨moleculeWord x,hl,literalClosure_to_finiteReversible _ x hx⟩
  · rintro ⟨w,hw,hg⟩
    obtain ⟨x,hx,he⟩ := finiteReversible_to_literalClosure hg
    exact ⟨x,hx,by simpa [he] using hw⟩

theorem quotient_escape_tendsto (a : I) :
    Filter.Tendsto (fun K => quotientStaticMeasure (2*(K+2)) a (quotientEscapeEvent 2 K))
      Filter.atTop (nhds (quotientSurvival a)) := by
  simp_rw [quotient_escape_measure_eq,quotientSurvival_eq]
  exact reversible_escape_probability_tendsto (quotientInfiniteMeasure a) 2

end RAFReactionQuotient
