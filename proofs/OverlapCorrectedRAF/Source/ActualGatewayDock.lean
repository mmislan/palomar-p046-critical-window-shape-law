module

public import proofs.OverlapCorrectedRAF.Source.RepositorySemanticCounting
public import proofs.OverlapCorrectedRAF.Asymptotic.GatewayProbability

@[expose] public section

namespace OverlapCorrectedRAF.Source

open RAF RAF.Polymer RAF.Concrete
open OverlapCorrectedRAF.Overlap

def repositorySeedChannels (n t : Nat) : Finset (RepositoryChannel n) :=
  Finset.univ.filter fun r => RevSeedReaction (repositoryCRS n t) r

def lowerMolecule {n t : Nat} (x : Molecule n) (h : molLength x ≤ t) :
    Molecule t :=
  moleculeOfCode (by simp [molLength]) h x.2

@[simp] theorem molLength_lowerMolecule {n t : Nat} (x : Molecule n)
    (h : molLength x ≤ t) :
    molLength (lowerMolecule x h) = molLength x := by
  unfold lowerMolecule moleculeOfCode molLength
  dsimp

@[simp] theorem lowerMolecule_code {n t : Nat} (x : Molecule n)
    (h : molLength x ≤ t) :
    (lowerMolecule x h).2.val = x.2.val := by
  unfold lowerMolecule moleculeOfCode
  rfl

theorem lowerMolecule_injective_on {n t : Nat} {x y : Molecule n}
    {hx : molLength x ≤ t} {hy : molLength y ≤ t}
    (hxy : lowerMolecule x hx = lowerMolecule y hy) : x = y := by
  have hlen : molLength x = molLength y := by
    simpa only [molLength_lowerMolecule] using congrArg molLength hxy
  rcases x with ⟨xi, xv⟩
  rcases y with ⟨yi, yv⟩
  have hi : xi = yi := by
    apply Fin.ext
    have hval : xi.val + 1 = yi.val + 1 := by
      simpa only [molLength] using hlen
    omega
  subst yi
  have hcode := congrArg (fun z : Molecule t => z.2.val) hxy
  have hv : xv = yv := by
    apply Fin.ext
    simpa using hcode
  exact congrArg (Sigma.mk xi) hv

theorem repositorySeedChannel_factors_food {n : Nat}
    {r : RepositoryChannel n}
    (hseed : RevSeedReaction (repositoryCRS n 2) r) :
    r.1.1 ∈ binaryFood n 2 ∧ r.1.2 ∈ binaryFood n 2 := by
  rcases hseed with hlhs | hrhs
  · exact ⟨hlhs (by simp [repositoryCRS]),
      hlhs (by simp [repositoryCRS])⟩
  · have hp : concatMolecule r.1.1 r.1.2 r.2.1 ∈ binaryFood n 2 := by
      apply hrhs
      simp [repositoryCRS]
    simp only [binaryFood, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have hsum : molLength r.1.1 + molLength r.1.2 ≤ 2 := by
      simpa only [concatMolecule, molLength_moleculeOfCode] using hp
    omega

def repositorySeedChannelToGateway {n : Nat}
    (r : {r : RepositoryChannel n //
      RevSeedReaction (repositoryCRS n 2) r}) : RepositoryGateway 2 := by
  have hfood := repositorySeedChannel_factors_food r.2
  have hu : molLength r.1.1.1 ≤ 2 := by
    simpa [binaryFood] using hfood.1
  have hv : molLength r.1.1.2 ≤ 2 := by
    simpa [binaryFood] using hfood.2
  let u := lowerMolecule r.1.1.1 hu
  let v := lowerMolecule r.1.1.2 hv
  refine ⟨(u, v), ?_⟩
  rcases r.1.2.2 with hdisplay | hprecedes
  · left
    intro heq
    apply hdisplay
    simpa [displayedConcat, u, v] using heq
  · right
    rcases hprecedes with hlen | ⟨hlen, hcode⟩
    · left
      simpa [moleculePrecedes, u, v] using hlen
    · right
      exact ⟨by simpa [u, v] using hlen,
        by simpa [u, v] using hcode⟩

theorem repositorySeedChannelToGateway_injective {n : Nat} :
    Function.Injective (@repositorySeedChannelToGateway n) := by
  intro r s hrs
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · have hrfood := repositorySeedChannel_factors_food r.2
    have hsfood := repositorySeedChannel_factors_food s.2
    have hru : molLength r.1.1.1 ≤ 2 := by
      simpa [binaryFood] using hrfood.1
    have hsu : molLength s.1.1.1 ≤ 2 := by
      simpa [binaryFood] using hsfood.1
    exact lowerMolecule_injective_on (hx := hru) (hy := hsu) (by
      simpa [repositorySeedChannelToGateway] using
        congrArg (fun z : RepositoryGateway 2 => z.1.1) hrs)
  · have hrfood := repositorySeedChannel_factors_food r.2
    have hsfood := repositorySeedChannel_factors_food s.2
    have hrv : molLength r.1.1.2 ≤ 2 := by
      simpa [binaryFood] using hrfood.2
    have hsv : molLength s.1.1.2 ≤ 2 := by
      simpa [binaryFood] using hsfood.2
    exact lowerMolecule_injective_on (hx := hrv) (hy := hsv) (by
      simpa [repositorySeedChannelToGateway] using
        congrArg (fun z : RepositoryGateway 2 => z.1.2) hrs)

theorem repositorySeedChannels_card_le_34 (n : Nat) :
    (repositorySeedChannels n 2).card ≤ 34 := by
  rw [← card_repository_gateway_binary_t2]
  rw [repositorySeedChannels, ← Fintype.card_subtype]
  exact Fintype.card_le_of_injective repositorySeedChannelToGateway
    repositorySeedChannelToGateway_injective

/-- A seed channel is open exactly when its whole molecule fibre is asked to
be hit.  Keeping the ambient channel catalogue unchanged lets this event be
compared directly with the actual repository RAF catalogue. -/
def repositorySeedRequirements (n : Nat)
    (seed channel : RepositoryChannel n) : Finset (Molecule n) :=
  if channel = seed then Finset.univ else ∅

theorem selectedRequirementFamily_repositorySeed
    {n : Nat} (hM : (Finset.univ : Finset (Molecule n)).Nonempty)
    (selected : Finset (RepositoryChannel n)) (channel : RepositoryChannel n) :
    selectedRequirementFamily selected (repositorySeedRequirements n) channel =
      if channel ∈ selected then {Finset.univ} else ∅ := by
  classical
  ext W
  simp only [selectedRequirementFamily, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨seed, ⟨hseed, hactive⟩, hW⟩
    by_cases hcs : channel = seed
    · subst seed
      simp [hseed, repositorySeedRequirements] at hW ⊢
      exact hW.symm
    · simp [repositorySeedRequirements, hcs] at hactive
  · intro hW
    by_cases hc : channel ∈ selected
    · have hEq : W = Finset.univ := by simpa [hc] using hW
      subst W
      exact ⟨channel, ⟨hc, by simp [repositorySeedRequirements, hM]⟩,
        by simp [repositorySeedRequirements]⟩
    · simp [hc] at hW

theorem jointBernoulliHitProbability_repositorySeed
    {n : Nat} (hM : (Finset.univ : Finset (Molecule n)).Nonempty)
    (p : ℝ) (selected : Finset (RepositoryChannel n)) :
    jointBernoulliHitProbability p Finset.univ
        (repositorySeedRequirements n) selected =
      ∏ _seed ∈ selected,
        localHitProbability (1 - p) ({Finset.univ} : Finset (Finset (Molecule n))) := by
  classical
  rw [jointBernoulliHitProbability]
  simp_rw [selectedRequirementFamily_repositorySeed hM]
  symm
  calc
    _ = ∏ seed ∈ selected, localHitProbability (1 - p)
          (if seed ∈ selected then {Finset.univ} else ∅) := by
      apply Finset.prod_congr rfl
      intro seed hseed
      rw [ite_eq_left hseed]
    _ = _ := Fintype.prod_subset fun _seed hne => by
      by_contra hseed
      simp [hseed, localHitProbability_empty] at hne

theorem repositorySeed_intersections_factorize
    {n : Nat} (hM : (Finset.univ : Finset (Molecule n)).Nonempty)
    (p : ℝ) (selected : Finset (RepositoryChannel n)) :
    jointBernoulliHitProbability p Finset.univ
        (repositorySeedRequirements n) selected =
      ∏ seed ∈ selected,
        jointBernoulliHitProbability p Finset.univ
          (repositorySeedRequirements n) {seed} := by
  rw [jointBernoulliHitProbability_repositorySeed hM p selected]
  apply Finset.prod_congr rfl
  intro seed hseed
  rw [jointBernoulliHitProbability_repositorySeed hM p {seed}]
  simp

theorem repositorySeedOpenProbability_exact
    {n : Nat} (hM : (Finset.univ : Finset (Molecule n)).Nonempty)
    (p : ℝ) :
    rafBernoulliProbability p Finset.univ (repositorySeedChannels n 2)
        (repositorySeedRequirements n) =
      1 - (1 - p) ^
        (Fintype.card (Molecule n) * (repositorySeedChannels n 2).card) := by
  classical
  rw [rafBernoulliProbability_eq_source_nonoverlap p Finset.univ
    (repositorySeedChannels n 2) (repositorySeedRequirements n)
    (fun _ => Fintype.card (Molecule n)) (fun _ => 1)
    (fun selected _ => repositorySeed_intersections_factorize hM p selected)]
  · simp_rw [pow_one]
    simp only [sub_sub_cancel]
    rw [Finset.prod_const, ← pow_mul]
  · intro seed hseed
    rw [jointBernoulliHitProbability_repositorySeed hM p {seed}]
    rw [OverlapCorrectedRAF.Core.oneCoreBernoulliProbability_exact]
    simp only [Finset.prod_singleton, pow_one]
    rw [localHitProbability_singleton]
    simp

theorem repositoryRAFFibreConfigurations_subset_seedOpenConfigurations
    (n : Nat) :
    repositoryRAFFibreConfigurations n 2 ⊆
      catalogueFibreHitConfigurations Finset.univ
        (repositorySeedChannels n 2) (repositorySeedRequirements n) := by
  classical
  intro config hconfig
  have hexists : ∃ S : Finset (RepositoryChannel n),
      IsRevRAF (repositoryCRS n 2)
        (repositoryCatalysisOfFibreConfig config) S := by
    simpa [repositoryRAFFibreConfigurations] using hconfig
  obtain ⟨S, hraf⟩ := hexists
  obtain ⟨seed, hseed, x, hx⟩ :=
    repository_raf_has_catalyzed_gateway n 2
      (repositoryCatalysisOfFibreConfig config) S hraf
  have hM : (Finset.univ : Finset (Molecule n)).Nonempty :=
    ⟨x, Finset.mem_univ x⟩
  simp only [catalogueFibreHitConfigurations, Finset.mem_biUnion]
  refine ⟨seed, ?_, ?_⟩
  · simp [repositorySeedChannels, hseed]
  · apply Finset.mem_pi.mpr
    intro channel hchannel
    apply mem_fibreHitConfigurations_iff.mpr
    intro W hW
    rw [selectedRequirementFamily_repositorySeed hM] at hW
    by_cases hcs : channel = seed
    · subst channel
      have hWuniv : W = Finset.univ := by simpa using hW
      subst W
      apply Finset.not_disjoint_iff.mpr
      exact ⟨x, hx, Finset.mem_univ x⟩
    · simp [hcs] at hW

theorem jointFibreBernoulliWeight_nonneg
    {M J : Type*} [Fintype M] [DecidableEq J]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (channels : Finset J)
    (config : ∀ j, j ∈ channels → Finset M) :
    0 ≤ jointFibreBernoulliWeight p channels config := by
  rw [jointFibreBernoulliWeight]
  apply Finset.prod_nonneg
  intro j hj
  exact mul_nonneg (pow_nonneg hp0 _)
    (pow_nonneg (sub_nonneg.mpr hp1) _)

theorem repositoryRAFBernoulliProbability_le_seedOpen
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : Nat) :
    rafBernoulliProbability p Finset.univ
        (repositoryCoreSupports n 2) (repositorySupportRequirements n 2) ≤
      rafBernoulliProbability p Finset.univ
        (repositorySeedChannels n 2) (repositorySeedRequirements n) := by
  classical
  rw [repository_rafBernoulliProbability_eq_actual_raf_mass]
  rw [rafBernoulliProbability_eq_sum_catalogue_weights]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (repositoryRAFFibreConfigurations_subset_seedOpenConfigurations n)
    (fun config _ _ =>
      jointFibreBernoulliWeight_nonneg hp0 hp1 Finset.univ config)

theorem repositoryRAFBernoulliProbability_le_gateway
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {n : Nat} (hn : 1 ≤ n) :
    rafBernoulliProbability p Finset.univ
        (repositoryCoreSupports n 2) (repositorySupportRequirements n 2) ≤
      Asymptotic.repositoryGatewayOpenProbability p n := by
  have hM : (Finset.univ : Finset (Molecule n)).Nonempty := by
    let x : Molecule n := moleculeOfCode (L := 1) (by omega) hn (0 : Word 1)
    exact ⟨x, Finset.mem_univ x⟩
  refine (repositoryRAFBernoulliProbability_le_seedOpen hp0 hp1 n).trans ?_
  rw [repositorySeedOpenProbability_exact hM p]
  rw [Asymptotic.repositoryGatewayOpenProbability,
    RAF.Corrected.atLeastOneProbability,
    RAF.Probability.allAbsentProbability_eq_pow]
  apply sub_le_sub_left
  apply pow_le_pow_of_le_one (sub_nonneg.mpr hp1) (by linarith)
  exact Nat.mul_le_mul_left (Fintype.card (Molecule n))
    (repositorySeedChannels_card_le_34 n)

end OverlapCorrectedRAF.Source
