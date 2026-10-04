module

public import proofs.RAFReactionQuotient.FiniteApproximation
public import proofs.HordijkSteelThreshold.SourceTerminalRAF

@[expose] public section

namespace RAFReactionQuotient
open Classical Filter MeasureTheory unitInterval HordijkSteelThreshold
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open scoped ENNReal Topology

theorem quotient_same_field_seed_mass (N L m : ℕ) (a : I) :
    quotientStaticMeasure N a {q | ∀ w ∈ actualBinaryWords L,
      ∃ x ∈ quotientClosure N 2 (quotientOpen q), moleculeWord x = w} ≤
    quotientStaticMeasure N a {q | (m-1)*Fintype.card (Molecule N) ≤
      m*(quotientClosure N 2 (quotientOpen q)).card} +
    quotientStaticMeasure N a {q | m*(quotientClosure N L (quotientOpen q)).card <
      (m-1)*Fintype.card (Molecule N)} := by
  apply (measure_mono (show {q : RepositoryChannel N → Prop | ∀ w ∈ actualBinaryWords L,
      ∃ x ∈ quotientClosure N 2 (quotientOpen q), moleculeWord x = w} ⊆
      {q | (m-1)*Fintype.card (Molecule N) ≤ m*(quotientClosure N 2 (quotientOpen q)).card} ∪
      {q | m*(quotientClosure N L (quotientOpen q)).card < (m-1)*Fintype.card (Molecule N)} from ?_)).trans
      (measure_union_le _ _)
  intro q hseed
  by_cases hb : m*(quotientClosure N L (quotientOpen q)).card < (m-1)*Fintype.card (Molecule N)
  · exact Or.inr hb
  · left
    have hs : quotientClosure N L (quotientOpen q) ⊆ quotientClosure N 2 (quotientOpen q) := by
      simp only [quotientClosure_pullback] at hseed ⊢
      apply temporaryReactionClosure_seed_transfer Finset.Subset.rfl
      intro x hx
      have hw : moleculeWord x ∈ actualBinaryWords L :=
        (mem_actualBinaryWords _ _).mpr ⟨moleculeWord_nonempty x,by rwa [moleculeWord_length]⟩
      obtain ⟨y,hy,he⟩ := hseed _ hw
      exact moleculeWord_injective he ▸ hy
    exact (Nat.le_of_not_gt hb).trans (Nat.mul_le_mul_left m (Finset.card_le_card hs))

theorem quotient_capped_escape_le (N K : ℕ) (a : I) :
    quotientStaticMeasure N a {q | ∃ x ∈ quotientClosure N 2 (quotientOpen q), K+2 < molLength x} ≤
      quotientInfiniteMeasure a (reversibleEscapeEvent 2 K) := by
  rw [← infinite_quotient_restriction_map N a,
    Measure.map_apply (Measurable.of_eval (fun j => measurable_pi_apply _))
      (Set.toFinite _).measurableSet,
    quotientInfiniteMeasure,Measure.map_apply quotientField_measurable
      (measurableSet_reversibleEscapeEvent 2 K)]
  apply measure_mono
  intro ω h
  change ∃ x ∈ quotientClosure N 2 (quotientOpen (fun j => ω (quotientCoordinate j))),
    K+2 < molLength x at h
  rw [quotientClosure_restriction] at h
  obtain ⟨x,hx,hl⟩ := h
  apply (reversibleEscapeEvent_iff 2 K (quotientField ω)).mpr
  exact ⟨moleculeWord x,by simpa only [moleculeWord_length] using hl,
    finiteReversibleGenerated_to_infinite (literalClosure_to_finiteReversible _ x hx)⟩

theorem quotient_seed_le_survival_error (b0 : I) (hb0 : 0 < (b0 : ℝ))
    (m : ℕ) (hm : 2 ≤ m) :
    ∃ L : ℕ, 0 < L ∧ ∀ b : I, b0 ≤ b →
      quotientInfiniteMeasure b {field | ∀ w ∈ actualBinaryWords L,
        InfiniteReversibleGenerated 2 field w} ≤ quotientSurvival b + (m : ENNReal)⁻¹ := by
  obtain ⟨L,hL,hbulk⟩ := quotient_supplied_seed_bulk b0 hb0 m (by omega)
  refine ⟨L,hL,?_⟩
  intro b hb
  have hK (K : ℕ) :
      quotientInfiniteMeasure b {field | ∀ w ∈ actualBinaryWords L,
        InfiniteReversibleGenerated 2 field w} ≤
      quotientStaticMeasure (2*(K+2)) b (quotientEscapeEvent 2 K) + (m : ENNReal)⁻¹ := by
    apply le_of_tendsto (quotient_finite_seed_tendsto 2 b (actualBinaryWords L))
    filter_upwards [(tendsto_atTop.mp card_molecule_tendsto_atTop)
      (m*Fintype.card (Molecule (K+2))+1),eventually_ge_atTop 1] with N hlarge hN
    have hmass : quotientStaticMeasure N b {q | (m-1)*Fintype.card (Molecule N) ≤
        m*(quotientClosure N 2 (quotientOpen q)).card} ≤
        quotientStaticMeasure (2*(K+2)) b (quotientEscapeEvent 2 K) := by
      rw [quotient_escape_measure_eq]
      apply (measure_mono (show {q : RepositoryChannel N → Prop |
        (m-1)*Fintype.card (Molecule N) ≤ m*(quotientClosure N 2 (quotientOpen q)).card} ⊆
        {q | ∃ x ∈ quotientClosure N 2 (quotientOpen q), K+2 < molLength x} from ?_)).trans
        (quotient_capped_escape_le N K b)
      intro q hq
      by_contra h
      have hs : quotientClosure N 2 (quotientOpen q) ⊆ binaryFood N (K+2) := by
        intro x hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Nat.le_of_not_gt (fun hl => h ⟨x,hx,hl⟩)⟩
      have hc := (Finset.card_le_card hs).trans (binaryFood_card_le_cutoff N (K+2))
      change (m-1)*Fintype.card (Molecule N) ≤ m*(quotientClosure N 2 (quotientOpen q)).card at hq
      have hmult : Fintype.card (Molecule N) ≤ (m-1)*Fintype.card (Molecule N) := by
        have hh := Nat.mul_le_mul_right (Fintype.card (Molecule N)) (show 1 ≤ m-1 by omega)
        simpa using hh
      nlinarith
    exact (quotient_same_field_seed_mass N L m b).trans
      (add_le_add hmass (hbulk b hb N (by omega)))
  exact ge_of_tendsto' ((quotient_escape_tendsto b).add_const (m : ENNReal)⁻¹) hK

theorem quotient_uniform_seed_approximation (b0 : I) (hb0 : 0 < (b0 : ℝ))
    (m : ℕ) (hm : 2 ≤ m) :
    ∃ L : ℕ, 0 < L ∧ ∀ b : I, b0 ≤ b →
      quotientSurvival b ≤ quotientInfiniteMeasure b {field | ∀ w ∈ actualBinaryWords L,
        InfiniteReversibleGenerated 2 field w} ∧
      quotientInfiniteMeasure b {field | ∀ w ∈ actualBinaryWords L,
        InfiniteReversibleGenerated 2 field w} ≤ quotientSurvival b+(m : ENNReal)⁻¹ := by
  obtain ⟨L,hL,h⟩ := quotient_seed_le_survival_error b0 hb0 m hm
  refine ⟨L,hL,fun b hb => ⟨?_,h b hb⟩⟩
  exact quotientSurvival_le_seed b (hb0.trans_le hb) _
    (fun w hw => List.length_pos_iff.mpr ((mem_actualBinaryWords w L).mp hw).1)

end RAFReactionQuotient
