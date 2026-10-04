module

public import proofs.RAFCriticalWindowQuantitative.FiniteSeedEvaluation
public import proofs.RAFCriticalWindowQuantitative.QuotientEffectiveBulk
public import proofs.HordijkSteelThreshold.SourceStaticRAFBound
public import proofs.RAFReactionQuotient.SourceBounds

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open scoped ENNReal

theorem finite_food_seed_mass (N L m : ℕ) (a : I) :
    staticReactionMeasure N a {ω | binaryFood N L ⊆ temporaryReactionClosure 2 (staticOpenReactions ω)} ≤
      staticReactionMeasure N a {ω | (m-1)*Fintype.card (Molecule N) ≤
        m*(temporaryReactionClosure 2 (staticOpenReactions ω)).card} +
      staticReactionMeasure N a {ω | m*(temporaryReactionClosure L (staticOpenReactions ω)).card <
        (m-1)*Fintype.card (Molecule N)} := by
  apply (measure_mono (show {ω : Reaction N → Prop | binaryFood N L ⊆
      temporaryReactionClosure 2 (staticOpenReactions ω)} ⊆
      {ω | (m-1)*Fintype.card (Molecule N) ≤ m*(temporaryReactionClosure 2 (staticOpenReactions ω)).card} ∪
      {ω | m*(temporaryReactionClosure L (staticOpenReactions ω)).card < (m-1)*Fintype.card (Molecule N)} from ?_)).trans
    (measure_union_le _ _)
  intro ω hseed
  by_cases hb : m*(temporaryReactionClosure L (staticOpenReactions ω)).card < (m-1)*Fintype.card (Molecule N)
  · exact Or.inr hb
  · left
    have hs : temporaryReactionClosure L (staticOpenReactions ω) ⊆
        temporaryReactionClosure 2 (staticOpenReactions ω) := by
      apply temporaryReactionClosure_seed_transfer Finset.Subset.rfl
      intro x hx
      exact hseed (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩)
    exact (Nat.le_of_not_gt hb).trans (Nat.mul_le_mul_left m (Finset.card_le_card hs))

theorem quotient_finite_food_seed_mass (N L m : ℕ) (a : I) :
    quotientStaticMeasure N a {ω | binaryFood N L ⊆ quotientClosure N 2 (quotientOpen ω)} ≤
      quotientStaticMeasure N a {ω | (m-1)*Fintype.card (Molecule N) ≤
        m*(quotientClosure N 2 (quotientOpen ω)).card} +
      quotientStaticMeasure N a {ω | m*(quotientClosure N L (quotientOpen ω)).card <
        (m-1)*Fintype.card (Molecule N)} := by
  apply (measure_mono (show {ω : RepositoryChannel N → Prop | binaryFood N L ⊆ quotientClosure N 2 (quotientOpen ω)} ⊆
      {ω | (m-1)*Fintype.card (Molecule N) ≤ m*(quotientClosure N 2 (quotientOpen ω)).card} ∪
      {ω | m*(quotientClosure N L (quotientOpen ω)).card < (m-1)*Fintype.card (Molecule N)} from ?_)).trans
    (measure_union_le _ _)
  intro ω hseed
  by_cases hb : m*(quotientClosure N L (quotientOpen ω)).card < (m-1)*Fintype.card (Molecule N)
  · exact Or.inr hb
  · left
    have hs : quotientClosure N L (quotientOpen ω) ⊆ quotientClosure N 2 (quotientOpen ω) := by
      simp only [quotientClosure_pullback] at hseed ⊢
      apply temporaryReactionClosure_seed_transfer Finset.Subset.rfl
      intro x hx
      exact hseed (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩)
    exact (Nat.le_of_not_gt hb).trans (Nat.mul_le_mul_left m (Finset.card_le_card hs))

theorem split_finite_source_lower (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (lambda : ℝ)
    (hk : 6 < nearFullPoolSize n m)
    (hpool : rationalParameter q hq.le hq1 ≤ fixedPoolParameter (catalysisP n lambda) (nearFullPoolSize n m)) :
    staticReactionMeasure n (rationalParameter q hq.le hq1)
      {ω | binaryFood n (10*seedIndex q hq hq1 m) ⊆ temporaryReactionClosure 2 (staticOpenReactions ω)} ≤
      uniformCatalysisMeasure n lambda (HasRAFEvent n) + (m : ENNReal)⁻¹ := by
  have he : (finiteInitialSegment (Molecule n) (nearFullPoolSize n m)).card = nearFullPoolSize n m :=
    card_finiteInitialSegment _ _ (nearFullPoolSize_le n m)
  have hl := canonical_raf_ge_near_full_static n m lambda hm (rationalParameter q hq.le hq1) hk
    (by change _ ≤ fixedPoolParameter _ (finiteInitialSegment (Molecule n) (nearFullPoolSize n m)).card; rwa [he])
  exact (finite_food_seed_mass n _ m _).trans
    (add_le_add hl (effective_static_bulk q hq hq1 m hm n hn))

theorem quotient_finite_source_lower (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (p : I)
    (hk : 6 < nearFullPoolSize n m)
    (hpool : rationalParameter q hq.le hq1 ≤ fixedPoolParameter p (nearFullPoolSize n m)) :
    let hh : 0 < q/2 := by positivity
    let hh1 : q/2 ≤ 1 := by linarith
    quotientStaticMeasure n (rationalParameter q hq.le hq1)
      {ω | binaryFood n (10*seedIndex (q/2) hh hh1 m) ⊆ quotientClosure n 2 (quotientOpen ω)} ≤
      quotientRAFProbability n p + (m : ENNReal)⁻¹ := by
  dsimp only
  exact (quotient_finite_food_seed_mass n _ m _).trans
    (add_le_add (quotient_near_full_lower n m p _ hm hk hpool)
      (effective_quotient_bulk q hq hq1 m hm _ le_rfl n hn))

end RAFCriticalWindowQuantitative
