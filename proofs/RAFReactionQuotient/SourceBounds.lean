module

public import proofs.RAFReactionQuotient.PoolLaw
public import proofs.RAFReactionQuotient.SeedApproximation
public import proofs.HordijkSteelThreshold.NearFullPoolAsymptotics
public import proofs.OverlapCorrectedRAF.Source.ActualGatewayDock

@[expose] public section

set_option Elab.async false

namespace RAFReactionQuotient
open Classical Filter MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold
open RAF RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open scoped ENNReal Topology

def quotientRAFEvent (n : ℕ) : Set (RepositoryChannel n → Molecule n → Prop) :=
  {ω | ∃ S, IsRevRAF (repositoryCRS n 2) (fun x j => ω j x) S}

noncomputable def quotientRAFProbability (n : ℕ) (p : I) : ENNReal :=
  quotientCatalyticLaw n p (quotientRAFEvent n)

theorem quotient_static_barrier (n : ℕ) (p : I) (k : ℕ) (hk : 6 < k) :
    quotientStaticMeasure n (fixedPoolParameter p (finiteInitialSegment (Molecule n) k).card)
      {q | k ≤ (quotientClosure n 2 (quotientOpen q)).card} ≤ quotientRAFProbability n p := by
  apply (quotient_mass_ge_static n 2 p k (Fintype.card (RepositoryChannel n))).trans
  apply measure_mono
  intro ω hω
  exact quotient_terminal_hasRAF ω (hk.trans_le hω)

theorem quotient_near_full_lower (n m : ℕ) (p q : I) (hm : 0 < m)
    (hk : 6 < nearFullPoolSize n m)
    (hq : q ≤ fixedPoolParameter p (nearFullPoolSize n m)) :
    quotientStaticMeasure n q {ω | (m-1)*Fintype.card (Molecule n) ≤
      m*(quotientClosure n 2 (quotientOpen ω)).card} ≤ quotientRAFProbability n p := by
  let k := nearFullPoolSize n m
  have hmass : quotientStaticMeasure n q {ω | (m-1)*Fintype.card (Molecule n) ≤
      m*(quotientClosure n 2 (quotientOpen ω)).card} ≤
      quotientStaticMeasure n q {ω | k ≤ (quotientClosure n 2 (quotientOpen ω)).card} := by
    apply measure_mono
    intro ω hω
    change (m-1)*Fintype.card (Molecule n) ≤ m*(quotientClosure n 2 (quotientOpen ω)).card at hω
    have hd := Nat.div_mul_le_self (Fintype.card (Molecule n)) m
    have hp := Nat.mul_le_mul_left (m-1) hd
    dsimp [k,nearFullPoolSize]
    nlinarith
  have hmono := product_increasing_mono (fun _ : RepositoryChannel n => q)
    (fun _ => fixedPoolParameter p k) (fun _ => hq)
    (fun ω => k ≤ (quotientClosure n 2 (quotientOpen ω)).card) (by
      intro x y hxy hx
      apply hx.trans
      apply Finset.card_le_card
      apply quotientClosure_mono
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxy j (Finset.mem_filter.mp hj).2⟩)
  have he : (finiteInitialSegment (Molecule n) k).card = k :=
    card_finiteInitialSegment _ _ (nearFullPoolSize_le n m)
  have hbar := quotient_static_barrier n p k hk
  rw [he] at hbar
  exact hmass.trans (hmono.trans hbar)

theorem quotient_coordinate_probability (n : ℕ) (p : I) (j : RepositoryChannel n) (x : Molecule n) :
    quotientCatalyticLaw n p {ω | ω j x} = (toNNReal p : ENNReal) := by
  have hj := (measurePreserving_eval
    (fun _ : RepositoryChannel n => RAFEmergenceApprox.Generic.colLaw (Molecule n) p) j).map_eq
  have hx := (measurePreserving_eval (fun _ : Molecule n => ambientCoordLaw p) x).map_eq
  have he := congrArg (fun μ : Measure (Molecule n → Prop) => μ {v | v x}) hj
  rw [Measure.map_apply (measurable_pi_apply _) (Set.toFinite _).measurableSet] at he
  change quotientCatalyticLaw n p {ω | ω j x} =
    RAFEmergenceApprox.Generic.colLaw (Molecule n) p {v | v x} at he
  rw [he]
  have hh := congrArg (fun μ : Measure Prop => μ {True}) hx
  rw [Measure.map_apply (measurable_pi_apply _) (MeasurableSet.singleton _)] at hh
  simpa [RAFEmergenceApprox.Generic.colLaw,ambientCoordLaw] using hh

def quotientBoundedSeed (n K : ℕ) : Set (RepositoryChannel n → Molecule n → Prop) :=
  {ω | ∃ x : Molecule n, ∃ j : RepositoryChannel n,
    molLength x ≤ K ∧ RevSeedReaction (repositoryCRS n 2) j ∧ ω j x}

theorem quotient_bounded_seed_le (n K : ℕ) (p : I) :
    quotientCatalyticLaw n p (quotientBoundedSeed n K) ≤
      (Fintype.card (Molecule K) : ENNReal)*34*(toNNReal p : ENNReal) := by
  let J := ↥(binaryFood n K) × ↥(repositorySeedChannels n 2)
  let E : J → Set (RepositoryChannel n → Molecule n → Prop) := fun j => {ω | ω j.2.val j.1.val}
  have he : quotientBoundedSeed n K = ⋃ j : J, E j := by
    ext ω
    simp only [quotientBoundedSeed,Set.mem_ofPred_eq,Set.mem_iUnion,E]
    constructor
    · rintro ⟨x,r,hx,hr,hω⟩
      exact ⟨(⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩⟩,
        ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩⟩),hω⟩
    · rintro ⟨⟨x,r⟩,hω⟩
      exact ⟨x.val,r.val,(Finset.mem_filter.mp x.property).2,(Finset.mem_filter.mp r.property).2,hω⟩
  rw [he]
  calc
    _ ≤ ∑ j : J, quotientCatalyticLaw n p (E j) := measure_iUnion_fintype_le _ _
    _ = (Fintype.card J : ENNReal)*(toNNReal p : ENNReal) := by
      simp only [E,quotient_coordinate_probability,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ ≤ _ := by
      apply mul_le_mul_left
      have hc : Fintype.card J ≤ Fintype.card (Molecule K)*34 := by
        dsimp [J]
        rw [Fintype.card_prod,Fintype.card_coe,Fintype.card_coe]
        exact Nat.mul_le_mul (binaryFood_card_le_cutoff n K) (repositorySeedChannels_card_le_34 n)
      exact_mod_cast hc

theorem quotient_raf_upper (n K : ℕ) (p : I) :
    quotientRAFProbability n p ≤
      quotientStaticMeasure (2*(K+2)) (fixedPoolParameter p (Fintype.card (Molecule n)))
        (quotientEscapeEvent 2 K) + (Fintype.card (Molecule (K+2)) : ENNReal)*34*(toNNReal p : ENNReal) := by
  let E : Set (RepositoryChannel n → Molecule n → Prop) := {ω | ∃ x ∈
    quotientClosure n 2 (RAFEmergenceApprox.Generic.catalystActive ω Finset.univ), K+2 < molLength x}
  have hs : quotientRAFEvent n ⊆ E ∪ quotientBoundedSeed n (K+2) := by
    intro ω hraf
    by_cases he : ω ∈ E
    · exact Or.inl he
    · right
      obtain ⟨S,hS⟩ := hraf
      obtain ⟨r,hr,hseed⟩ := exists_rev_seed_of_foodGenerated _ S hS.1 hS.2.1
      obtain ⟨x,k,hx,hcat⟩ := hS.2.2 r hr
      have hsub := quotient_raf_subset_peeling ω hS 0
      have hx' := quotientClosure_mono n 2 hsub ((mem_quotientClosure S x).mpr ⟨k,hx⟩)
      exact ⟨x,r,Nat.le_of_not_gt (fun hl => he ⟨x,hx',hl⟩),hseed,hcat⟩
  have hb := (measure_mono hs).trans ((measure_union_le _ _).trans
    (add_le_add_right (quotient_bounded_seed_le n (K+2) p) _))
  apply hb.trans
  apply add_le_add_left
  change quotientCatalyticLaw n p {ω | ∃ x ∈ quotientClosure n 2
    (RAFEmergenceApprox.Generic.catalystActive ω Finset.univ), K+2 < molLength x} ≤ _
  rw [quotient_pool_statistic n p Finset.univ
    (fun A => ∃ x ∈ quotientClosure n 2 A, K+2 < molLength x),Finset.card_univ,
    quotient_escape_measure_eq]
  exact quotient_capped_escape_le n K _

end RAFReactionQuotient
