module

public import proofs.RAFCriticalWindowQuantitative.QuotientEffectiveBulk
public import proofs.RAFReactionQuotient.SeedApproximation

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical Filter MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold RAFReactionQuotient
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open scoped ENNReal Topology

theorem effective_quotient_seed_survival (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m : ℕ) (hm : 2 ≤ m) :
    let hhalf : 0 < q/2 := by positivity
    let hhalf1 : q/2 ≤ 1 := by linarith
    let L := 10*seedIndex (q/2) hhalf hhalf1 m
    ∀ b : I, rationalParameter q hq.le hq1 ≤ b →
      quotientInfiniteMeasure b {field | ∀ w ∈ actualBinaryWords L,
        InfiniteReversibleGenerated 2 field w} ≤ quotientSurvival b + (m : ENNReal)⁻¹ := by
  dsimp only
  have hhalf : 0 < q/2 := by positivity
  have hhalf1 : q/2 ≤ 1 := by linarith
  let L := 10*seedIndex (q/2) hhalf hhalf1 m
  have hbulk := effective_quotient_bulk q hq hq1 m (by omega)
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

end RAFCriticalWindowQuantitative
