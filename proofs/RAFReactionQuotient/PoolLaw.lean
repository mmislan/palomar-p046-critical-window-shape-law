module

public import proofs.RAFReactionQuotient.Terminal
public import proofs.HordijkSteelThreshold.FixedPoolReactionLaw

@[expose] public section

set_option Elab.async false

namespace RAFReactionQuotient
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

theorem quotient_pool_column_map (n : ℕ) (p : I) (C : Finset (Molecule n)) :
    (RAFEmergenceApprox.Generic.colLaw (Molecule n) p).map (fun v => ∃ x ∈ C, v x) =
      ambientCoordLaw (fixedPoolParameter p C.card) := by
  apply probability_prop_eq_of_false
  rw [Measure.map_apply (measurable_of_finite _) (MeasurableSet.singleton _)]
  have he : (fun v : Molecule n → Prop => ∃ x ∈ C, v x) ⁻¹' {False} =
      {v | ¬ ∃ x ∈ C, v x} := by ext v; simp
  rw [he,RAFEmergenceApprox.Generic.closed_probability,ambientCoordLaw_false]
  simp [fixedPoolParameter,← ENNReal.coe_pow]
  apply NNReal.eq
  simp

theorem quotient_pool_map (n : ℕ) (p : I) (C : Finset (Molecule n)) :
    (quotientCatalyticLaw n p).map (fun ω j => ∃ x ∈ C, ω j x) =
      quotientStaticMeasure n (fixedPoolParameter p C.card) := by
  change (Measure.pi (fun _ : RepositoryChannel n => RAFEmergenceApprox.Generic.colLaw (Molecule n) p)).map
      (fun ω j => ∃ x ∈ C, ω j x) = _
  rw [Measure.pi_map_pi
    (μ := fun _ : RepositoryChannel n => RAFEmergenceApprox.Generic.colLaw (Molecule n) p)
    (f := fun (_ : RepositoryChannel n) (v : Molecule n → Prop) => ∃ x ∈ C, v x)
    (fun _ => (measurable_of_finite _).aemeasurable)]
  simp_rw [quotient_pool_column_map]
  rfl

theorem quotient_pool_statistic (n : ℕ) (p : I) (C : Finset (Molecule n))
    (stat : Finset (RepositoryChannel n) → Prop) :
    quotientCatalyticLaw n p {ω | stat (RAFEmergenceApprox.Generic.catalystActive ω C)} =
      quotientStaticMeasure n (fixedPoolParameter p C.card) {q | stat (quotientOpen q)} := by
  rw [← quotient_pool_map n p C,Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
  rfl

theorem quotient_peeling_statistic (n L : ℕ) (p : I) (T : ℕ)
    (stat : Finset (RepositoryChannel n) → Prop) :
    quotientCatalyticLaw n p {ω | stat (peelingActiveAt
      (RAFEmergenceApprox.Generic.catalystActive ω) (quotientClosure n L) T)} =
    quotientCatalyticLaw n p {ω | stat (peelingActiveAt
      (fun C => RAFEmergenceApprox.Generic.catalystActive ω (finiteInitialSegment (Molecule n) C.card))
      (quotientClosure n L) T)} := by
  let E : Set (Fin (T+1) → RepositoryChannel n → Prop) :=
    {H | stat (Finset.univ.filter (H ⟨T,Nat.lt_succ_self T⟩))}
  have he := congrArg (fun μ : Measure (Fin (T+1) → RepositoryChannel n → Prop) => μ E)
    (quotient_history_map n L p T)
  rw [Measure.map_apply (measurable_of_finite _) (Set.toFinite E).measurableSet,
    Measure.map_apply (measurable_of_finite _) (Set.toFinite E).measurableSet] at he
  have hfinal (response : Finset (Molecule n) → Finset (RepositoryChannel n)) :
      Finset.univ.filter (activeTrace response (quotientClosure n L) T
        ⟨T,Nat.lt_succ_self T⟩) = peelingActiveAt response (quotientClosure n L) T := by
    ext r
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,activeTrace]
  simpa only [E,Set.preimage,Set.mem_ofPred_eq,hfinal] using he

theorem quotient_mass_ge_static (n L : ℕ) (p : I) (k T : ℕ) :
    quotientStaticMeasure n (fixedPoolParameter p (finiteInitialSegment (Molecule n) k).card)
      {q | k ≤ (quotientClosure n L (quotientOpen q)).card} ≤
    quotientCatalyticLaw n p {ω | k ≤ (quotientClosure n L (peelingActiveAt
      (RAFEmergenceApprox.Generic.catalystActive ω) (quotientClosure n L) T)).card} := by
  rw [← quotient_pool_statistic n p (finiteInitialSegment (Molecule n) k)
      (fun A => k ≤ (quotientClosure n L A).card),
    quotient_peeling_statistic n L p T (fun A => k ≤ (quotientClosure n L A).card)]
  apply measure_mono
  intro ω hω
  have hm : Monotone (fun k => RAFEmergenceApprox.Generic.catalystActive ω
      (finiteInitialSegment (Molecule n) k)) :=
    (RAFEmergenceApprox.Generic.catalystActive_mono ω).comp (finiteInitialSegment_mono _)
  have hs := RAFEmergenceApprox.scalar_barrier_subset _ (quotientClosure n L) hm
    (quotientClosure_mono n L) k (hω.trans (Finset.card_le_univ _)) hω T
  exact hω.trans (Finset.card_le_card (quotientClosure_mono n L hs))

end RAFReactionQuotient
