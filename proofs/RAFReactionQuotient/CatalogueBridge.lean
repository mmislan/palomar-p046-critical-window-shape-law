module

public import proofs.RAFReactionQuotient.SourceBounds
public import proofs.HordijkSteelThreshold.StaticEventContinuity

@[expose] public section

set_option Elab.async false

namespace RAFReactionQuotient
open Classical MeasureTheory unitInterval HordijkSteelThreshold RAF.Polymer
open OverlapCorrectedRAF.Source OverlapCorrectedRAF.Overlap

instance quotientCatalytic_probability (n : ℕ) (p : I) :
    IsProbabilityMeasure (quotientCatalyticLaw n p) := by
  unfold quotientCatalyticLaw
  infer_instance

noncomputable def fibreConfigEquiv (n : ℕ) :
    (RepositoryChannel n → Molecule n → Prop) ≃
      (∀ r, r ∈ (Finset.univ : Finset (RepositoryChannel n)) → Finset (Molecule n)) where
  toFun ω r _ := Finset.univ.filter (ω r)
  invFun c r x := x ∈ c r (Finset.mem_univ r)
  left_inv ω := by funext r x; simp
  right_inv c := by funext r hr; ext x; simp

theorem fibreConfig_catalysis (n : ℕ) (ω : RepositoryChannel n → Molecule n → Prop) :
    repositoryCatalysisOfFibreConfig (fibreConfigEquiv n ω) = (fun x j => ω j x) := by
  funext x j
  simp [repositoryCatalysisOfFibreConfig,fibreConfigEquiv]

theorem quotient_column_atom_real (n : ℕ) (p : I) (v : Molecule n → Prop) :
    (RAFEmergenceApprox.Generic.colLaw (Molecule n) p {v}).toReal =
      fibreBernoulliWeight (p : ℝ) (Finset.univ.filter v) := by
  rw [RAFEmergenceApprox.Generic.colLaw,Measure.pi_singleton,ENNReal.toReal_prod]
  simp only [ambientCoordLaw_atom,ENNReal.coe_toReal]
  have hw (x : Molecule n) : (staticAtomWeight p (v x) : ℝ) =
      if v x then (p : ℝ) else 1-(p : ℝ) := by
    by_cases hx : v x <;> simp [staticAtomWeight,hx]
  simp_rw [hw]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  unfold fibreBernoulliWeight
  congr 2
  have he := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Molecule n))) v
  rw [Finset.card_univ] at he
  omega

theorem quotient_catalytic_atom_real (n : ℕ) (p : I) (ω : RepositoryChannel n → Molecule n → Prop) :
    (quotientCatalyticLaw n p {ω}).toReal =
      jointFibreBernoulliWeight (p : ℝ) Finset.univ (fibreConfigEquiv n ω) := by
  rw [quotientCatalyticLaw,RAFEmergenceApprox.Generic.law,Measure.pi_singleton,ENNReal.toReal_prod]
  simp_rw [quotient_column_atom_real]
  simp [jointFibreBernoulliWeight,fibreConfigEquiv]

theorem quotient_probability_eq_catalogue (n : ℕ) (p : I) :
    (quotientRAFProbability n p).toReal = rafBernoulliProbability (p : ℝ) Finset.univ
      (repositoryCoreSupports n 2) (repositorySupportRequirements n 2) := by
  rw [repository_rafBernoulliProbability_eq_actual_raf_mass]
  let F : Finset (RepositoryChannel n → Molecule n → Prop) :=
    Finset.univ.filter (fun ω => ω ∈ quotientRAFEvent n)
  have hF : (F : Set (RepositoryChannel n → Molecule n → Prop)) = quotientRAFEvent n := by
    ext ω; simp [F]
  have hs : (quotientRAFProbability n p).toReal =
      ∑ ω ∈ F, (quotientCatalyticLaw n p {ω}).toReal := by
    unfold quotientRAFProbability
    rw [← hF,← sum_measure_singleton,ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
  rw [hs]
  simp_rw [quotient_catalytic_atom_real]
  apply Finset.sum_bij (fun ω _ => fibreConfigEquiv n ω)
  · intro ω hω
    simp only [repositoryRAFFibreConfigurations,Finset.mem_filter,Finset.mem_univ,true_and,
      fibreConfig_catalysis]
    exact (Finset.mem_filter.mp hω).2
  · intro ω _ η _ he
    exact (fibreConfigEquiv n).injective he
  · intro c hc
    refine ⟨(fibreConfigEquiv n).symm c,?_,(fibreConfigEquiv n).apply_symm_apply c⟩
    have hc' : ∃ S, RAF.Concrete.IsRevRAF (repositoryCRS n 2)
        (repositoryCatalysisOfFibreConfig c) S := by
      simpa only [repositoryRAFFibreConfigurations,Finset.mem_filter,Finset.mem_univ,
        true_and] using hc
    have hcat : repositoryCatalysisOfFibreConfig c =
        (fun x j => ((fibreConfigEquiv n).symm c) j x) := by
      simpa only [(fibreConfigEquiv n).apply_symm_apply] using
        fibreConfig_catalysis n ((fibreConfigEquiv n).symm c)
    have hc'' : ∃ S, RAF.Concrete.IsRevRAF (repositoryCRS n 2)
        (fun x j => ((fibreConfigEquiv n).symm c) j x) S := by
      rw [← hcat]
      exact hc'
    have hmem : (fibreConfigEquiv n).symm c ∈ quotientRAFEvent n := hc''
    have hmemF : (fibreConfigEquiv n).symm c ∈ (F : Set _) := by
      rw [hF]
      exact hmem
    exact hmemF
  · intro ω _
    rfl

end RAFReactionQuotient
