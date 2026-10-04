module

public import proofs.RAFCriticalWindowQuantitative.EffectiveBulk
public import proofs.RAFReactionQuotient.SeedBulk

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold RAFReactionQuotient
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open scoped ENNReal

/-- Explicit seed cutoff transported through the source's bounded-fibre domination. -/
theorem effective_quotient_bulk (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
    (m : ℕ) (hm : 0 < m) :
    let hhalf : 0 < q/2 := by positivity
    let hhalf1 : q/2 ≤ 1 := by linarith
    let L := 10*seedIndex (q/2) hhalf hhalf1 m
    ∀ a : I, rationalParameter q hq.le hq1 ≤ a → ∀ n : ℕ, 0 < n →
      quotientStaticMeasure n a {ω |
        m*(quotientClosure n L (quotientOpen ω)).card <
          (m-1)*Fintype.card (Molecule n)} ≤ (m : ENNReal)⁻¹ := by
  dsimp only
  have hhalf : 0 < q/2 := by positivity
  have hhalf1 : q/2 ≤ 1 := by linarith
  let a0 := rationalParameter q hq.le hq1
  let L := 10*seedIndex (q/2) hhalf hhalf1 m
  have heq : rationalParameter (q/2) hhalf.le hhalf1 = halfParameter a0 := by
    apply Subtype.ext
    simp [rationalParameter,halfParameter,a0]
  have hbulk := effective_static_bulk (q/2) hhalf hhalf1 m hm
  dsimp only at hbulk
  rw [heq] at hbulk
  intro a ha n hn
  let E := fun ω : RepositoryChannel n → Prop =>
    m*(quotientClosure n L (quotientOpen ω)).card < (m-1)*Fintype.card (Molecule n)
  have hi := product_decreasing_mono
    (fibreParameter (@splitToQuotient n) (halfParameter a0)) (fun _ => a)
    (fun j => (fibreParameter_half_le splitToQuotient a0 j
      (by
        convert split_fibre_le_two j using 1
        congr 1
        ext r
        simp)).trans ha)
    E (quotient_mass_failure_antitone n L m)
  have he := fieldOR_map (@splitToQuotient n) (halfParameter a0)
  rw [← he, Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet] at hi
  have hevent : {ω : Reaction n → Prop | E (fieldOR splitToQuotient ω)} =
      {ω | m*(temporaryReactionClosure L (staticOpenReactions ω)).card <
        (m-1)*Fintype.card (Molecule n)} := by
    ext ω
    simp only [Set.mem_ofPred_eq,E,quotientClosure_OR]
  change quotientStaticMeasure n a {ω | E ω} ≤
    RAFEmergenceApprox.Generic.colLaw (Reaction n) (halfParameter a0)
      {ω | E (fieldOR splitToQuotient ω)} at hi
  rw [hevent] at hi
  apply hi.trans
  simpa only [staticReactionMeasure,Measure.infinitePi_eq_pi,
    RAFEmergenceApprox.Generic.colLaw] using hbulk n hn

end RAFCriticalWindowQuantitative
