module

public import proofs.RAFReactionQuotient.ProductDomination
public import proofs.RAFReactionQuotient.History
public import proofs.RAFReactionQuotient.Fibres
public import proofs.HordijkSteelThreshold.StaticBulk

@[expose] public section

namespace RAFReactionQuotient
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

theorem product_decreasing_mono {J : Type*} [Fintype J]
    (a c : J → I) (hac : ∀ j, a j ≤ c j)
    (E : (J → Prop) → Prop) (hE : Antitone E) :
    (Measure.pi (fun j => ambientCoordLaw (c j))) {ω | E ω} ≤
      (Measure.pi (fun j => ambientCoordLaw (a j))) {ω | E ω} := by
  have hg : Monotone (fun ω => ¬ E ω) := by
    intro x y hxy hx hy
    exact hx (hE hxy hy)
  have hi := product_increasing_mono a c hac (fun ω => ¬ E ω) hg
  have hc (q : J → I) : (Measure.pi (fun j => ambientCoordLaw (q j))) {ω | E ω} =
      1-(Measure.pi (fun j => ambientCoordLaw (q j))) {ω | ¬ E ω} := by
    have he : {ω | E ω} = {ω | ¬ E ω}ᶜ := by ext ω; simp
    rw [he,measure_compl (Set.toFinite _).measurableSet (measure_ne_top _ _),measure_univ]
  rw [hc a,hc c]
  exact tsub_le_tsub_left hi 1

noncomputable def quotientStaticMeasure (n : ℕ) (a : I) :=
  Measure.pi (fun _ : RepositoryChannel n => ambientCoordLaw a)

noncomputable def quotientOpen {n : ℕ} (ω : RepositoryChannel n → Prop) :
    Finset (RepositoryChannel n) := Finset.univ.filter ω

theorem quotientOpen_OR {n : ℕ} (ω : Reaction n → Prop) :
    quotientOpen (fieldOR splitToQuotient ω) =
      (staticOpenReactions ω).image splitToQuotient := by
  ext j
  simp [quotientOpen,fieldOR,staticOpenReactions,and_comm]

theorem quotientClosure_OR {n L : ℕ} (ω : Reaction n → Prop) :
    quotientClosure n L (quotientOpen (fieldOR splitToQuotient ω)) =
      temporaryReactionClosure L (staticOpenReactions ω) := by
  rw [quotientOpen_OR]
  ext x
  simp only [mem_quotientClosure,mem_temporaryReactionClosure,split_closure_eq_quotient]

theorem quotient_mass_failure_antitone (n L m : ℕ) :
    Antitone (fun ω : RepositoryChannel n → Prop =>
      m*(quotientClosure n L (quotientOpen ω)).card < (m-1)*Fintype.card (Molecule n)) := by
  intro x y hxy hy
  have hs : quotientOpen x ⊆ quotientOpen y := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxy j (Finset.mem_filter.mp hj).2⟩
  have hc := Nat.mul_le_mul_left m (Finset.card_le_card (quotientClosure_mono n L hs))
  exact lt_of_le_of_lt hc hy

/-- One fixed seed at each positive lower openness works for all larger
opennesses and all positive caps. No quotient bulk hypothesis is assumed. -/
theorem quotient_supplied_seed_bulk (a0 : I) (ha0 : 0 < (a0 : ℝ))
    (m : ℕ) (hm : 0 < m) :
    ∃ L : ℕ, 0 < L ∧ ∀ a : I, a0 ≤ a → ∀ n : ℕ, 0 < n →
      quotientStaticMeasure n a {ω |
        m*(quotientClosure n L (quotientOpen ω)).card <
          (m-1)*Fintype.card (Molecule n)} ≤ (m : ENNReal)⁻¹ := by
  have hh : 0 < (halfParameter a0 : ℝ) := by
    change 0 < (a0 : ℝ)/2
    positivity
  obtain ⟨L,hL,hbulk⟩ := static_bulk_near_full (halfParameter a0) hh m hm
  refine ⟨L,hL,?_⟩
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

end RAFReactionQuotient
