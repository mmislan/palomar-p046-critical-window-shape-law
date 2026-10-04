module

public import proofs.OverlapCorrectedRAF.Overlap.SemanticCounting
public import proofs.OverlapCorrectedRAF.Source.KauffmanRepositoryCRS

@[expose] public section

namespace OverlapCorrectedRAF.Source

open RAF RAF.Polymer RAF.Concrete
open OverlapCorrectedRAF.Overlap

/-- The finite molecule support of a reversible reaction family. -/
def revCoreMolecules {M R : Type*} [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) : Finset M :=
  Q.food ∪ S.biUnion fun r => Q.lhs r ∪ Q.rhs r

theorem revClosureAt_subset_revCoreMolecules
    {M R : Type*} [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) :
    ∀ k, revClosureAt Q S k ⊆ revCoreMolecules Q S := by
  intro k
  induction k with
  | zero =>
      intro x hx
      exact Finset.mem_union_left _ hx
  | succ k ih =>
      intro x hx
      simp only [revClosureAt, revClosureStep, Finset.mem_union,
        Finset.mem_biUnion] at hx
      rcases hx with hx | ⟨r, hr, hx⟩
      · exact ih hx
      · simp only [revCoreMolecules, Finset.mem_union, Finset.mem_biUnion]
        right
        refine ⟨r, hr, ?_⟩
        by_cases hl : RevEnabledLhs Q (revClosureAt Q S k) r <;>
          by_cases hr' : RevEnabledRhs Q (revClosureAt Q S k) r <;>
          simp [hl, hr'] at hx ⊢ <;> aesop

theorem mem_revCoreMolecules_iff_reachable
    {M R : Type*} [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) (hfg : RevFoodGenerated Q S)
    (x : M) :
    x ∈ revCoreMolecules Q S ↔ ∃ k, x ∈ revClosureAt Q S k := by
  constructor
  · intro hx
    simp only [revCoreMolecules, Finset.mem_union, Finset.mem_biUnion] at hx
    rcases hx with hx | ⟨r, hr, hx⟩
    · exact ⟨0, hx⟩
    · obtain ⟨k, hk⟩ := hfg r hr
      exact ⟨k, hk (by simpa using hx)⟩
  · rintro ⟨k, hx⟩
    exact revClosureAt_subset_revCoreMolecules Q S k hx

/-- Catalysis relation represented by its molecule subset in every repository
channel fibre. -/
def repositoryCatalysisOfFibreConfig {n : Nat}
    (config : ∀ r, r ∈ (Finset.univ : Finset (RepositoryChannel n)) →
      Finset (Molecule n)) : RepositoryCatalysis n :=
  fun x r => x ∈ config r (Finset.mem_univ r)

/-- Requirements derived from a literal repository support: used channels ask
to be hit by a molecule reachable from food through that support. -/
def repositorySupportRequirements (n t : Nat)
    (S : Finset (RepositoryChannel n)) (r : RepositoryChannel n) :
    Finset (Molecule n) :=
  if r ∈ S then revCoreMolecules (repositoryCRS n t) S else ∅

/-- Exhaustive deterministic catalogue of nonempty food-generated repository
supports. -/
noncomputable def repositoryCoreSupports (n t : Nat) :
    Finset (Finset (RepositoryChannel n)) :=
  by
    classical
    exact Finset.univ.filter fun S =>
      S.Nonempty ∧ RevFoodGenerated (repositoryCRS n t) S

theorem repositoryCoreMolecules_nonempty_of_mem {n t : Nat}
    {S : Finset (RepositoryChannel n)} {r : RepositoryChannel n}
    (hr : r ∈ S) :
    (revCoreMolecules (repositoryCRS n t) S).Nonempty := by
  refine ⟨concatMolecule r.1.1 r.1.2 r.2.1, ?_⟩
  simp only [revCoreMolecules, Finset.mem_union]
  right
  simp only [Finset.mem_biUnion]
  exact ⟨r, hr, by simp [repositoryCRS]⟩

theorem mem_singleton_repository_support_iff {n t : Nat}
    {S : Finset (RepositoryChannel n)}
    (config : ∀ r, r ∈ (Finset.univ : Finset (RepositoryChannel n)) →
      Finset (Molecule n)) :
    config ∈ jointFibreHitConfigurations Finset.univ
        (repositorySupportRequirements n t) {S} ↔
      ∀ r ∈ S, ∃ x,
        x ∈ config r (Finset.mem_univ r) ∧
        x ∈ revCoreMolecules (repositoryCRS n t) S := by
  classical
  constructor
  · intro h r hr
    have hfibre := (Finset.mem_pi.mp h) r (Finset.mem_univ r)
    have hhits := mem_fibreHitConfigurations_iff.mp hfibre
    have hreq : revCoreMolecules (repositoryCRS n t) S ∈
        selectedRequirementFamily {S} (repositorySupportRequirements n t) r := by
      simp only [selectedRequirementFamily, Finset.mem_image,
        Finset.mem_filter, Finset.mem_singleton]
      have hnonempty : (repositorySupportRequirements n t S r).Nonempty := by
        simpa [repositorySupportRequirements, hr] using
          (repositoryCoreMolecules_nonempty_of_mem (n := n) (t := t) hr)
      refine ⟨S, ⟨rfl, hnonempty⟩, ?_⟩
      simp [repositorySupportRequirements, hr]
    exact Finset.not_disjoint_iff.mp (hhits _ hreq)
  · intro h
    apply Finset.mem_pi.mpr
    intro r hrUniv
    apply mem_fibreHitConfigurations_iff.mpr
    intro W hW
    simp only [selectedRequirementFamily, Finset.mem_image,
      Finset.mem_filter, Finset.mem_singleton] at hW
    obtain ⟨k, ⟨hk, hkNonempty⟩, hkW⟩ := hW
    have hkS : k = S := hk
    subst k
    rw [← hkW]
    by_cases hr : r ∈ S
    · rw [repositorySupportRequirements, ite_eq_left hr]
      exact Finset.not_disjoint_iff.mpr (h r hr)
    · simp [repositorySupportRequirements, hr] at hkNonempty

theorem repository_support_hits_iff_autocatalytic {n t : Nat}
    {S : Finset (RepositoryChannel n)}
    (hfg : RevFoodGenerated (repositoryCRS n t) S)
    (config : ∀ r, r ∈ (Finset.univ : Finset (RepositoryChannel n)) →
      Finset (Molecule n)) :
    (∀ r ∈ S, ∃ x,
        x ∈ config r (Finset.mem_univ r) ∧
        x ∈ revCoreMolecules (repositoryCRS n t) S) ↔
      RevReflexivelyAutocatalytic (repositoryCRS n t)
        (repositoryCatalysisOfFibreConfig config) S := by
  constructor
  · intro h r hr
    obtain ⟨x, hxConfig, hxCore⟩ := h r hr
    obtain ⟨k, hxReach⟩ :=
      (mem_revCoreMolecules_iff_reachable (repositoryCRS n t) S hfg x).mp hxCore
    exact ⟨x, k, hxReach, hxConfig⟩
  · intro h r hr
    obtain ⟨x, k, hxReach, hxConfig⟩ := h r hr
    refine ⟨x, hxConfig, ?_⟩
    exact (mem_revCoreMolecules_iff_reachable
      (repositoryCRS n t) S hfg x).mpr ⟨k, hxReach⟩

theorem mem_singleton_repository_support_iff_isRevRAF {n t : Nat}
    {S : Finset (RepositoryChannel n)}
    (hS : S ∈ repositoryCoreSupports n t)
    (config : ∀ r, r ∈ (Finset.univ : Finset (RepositoryChannel n)) →
      Finset (Molecule n)) :
    config ∈ jointFibreHitConfigurations Finset.univ
        (repositorySupportRequirements n t) {S} ↔
      IsRevRAF (repositoryCRS n t)
        (repositoryCatalysisOfFibreConfig config) S := by
  classical
  have hmeta : S.Nonempty ∧ RevFoodGenerated (repositoryCRS n t) S := by
    simpa [repositoryCoreSupports] using hS
  rw [mem_singleton_repository_support_iff]
  rw [repository_support_hits_iff_autocatalytic hmeta.2]
  exact ⟨fun h => ⟨hmeta.1, hmeta.2, h⟩, fun h => h.2.2⟩

theorem mem_repository_catalogue_iff_exists_isRevRAF {n t : Nat}
    (config : ∀ r, r ∈ (Finset.univ : Finset (RepositoryChannel n)) →
      Finset (Molecule n)) :
    config ∈ catalogueFibreHitConfigurations Finset.univ
        (repositoryCoreSupports n t) (repositorySupportRequirements n t) ↔
      ∃ S : Finset (RepositoryChannel n),
        IsRevRAF (repositoryCRS n t)
          (repositoryCatalysisOfFibreConfig config) S := by
  classical
  constructor
  · intro h
    simp only [catalogueFibreHitConfigurations, Finset.mem_biUnion] at h
    obtain ⟨S, hS, hactive⟩ := h
    exact ⟨S, (mem_singleton_repository_support_iff_isRevRAF hS config).mp hactive⟩
  · rintro ⟨S, hraf⟩
    have hS : S ∈ repositoryCoreSupports n t := by
      simp only [repositoryCoreSupports, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨hraf.1, hraf.2.1⟩
    simp only [catalogueFibreHitConfigurations, Finset.mem_biUnion]
    exact ⟨S, hS,
      (mem_singleton_repository_support_iff_isRevRAF hS config).mpr hraf⟩

noncomputable def repositoryRAFFibreConfigurations (n t : Nat) :
    Finset (∀ r, r ∈ (Finset.univ : Finset (RepositoryChannel n)) →
      Finset (Molecule n)) := by
  classical
  exact Finset.univ.filter fun config =>
    ∃ S : Finset (RepositoryChannel n),
      IsRevRAF (repositoryCRS n t)
        (repositoryCatalysisOfFibreConfig config) S

theorem repository_catalogue_eq_raf_configurations (n t : Nat) :
    catalogueFibreHitConfigurations Finset.univ
        (repositoryCoreSupports n t) (repositorySupportRequirements n t) =
      repositoryRAFFibreConfigurations n t := by
  classical
  ext config
  rw [mem_repository_catalogue_iff_exists_isRevRAF]
  simp [repositoryRAFFibreConfigurations]

theorem repository_rafFixedQProbability_eq_actual_raf_ratio
    (n t Q : Nat) :
    rafFixedQProbability (Finset.univ : Finset (RepositoryChannel n))
        (repositoryCoreSupports n t) (repositorySupportRequirements n t) Q =
      ((repositoryRAFFibreConfigurations n t).filter fun config =>
          (∑ r ∈ (Finset.univ : Finset (RepositoryChannel n)).attach,
            (config r.1 r.2).card) = Q).card /
        Nat.choose (Fintype.card (Molecule n) *
          Fintype.card (RepositoryChannel n)) Q := by
  rw [rafFixedQProbability_eq_actual_catalogue_ratio]
  rw [repository_catalogue_eq_raf_configurations]
  simp

theorem repository_rafBernoulliProbability_eq_actual_raf_mass
    (p : ℝ) (n t : Nat) :
    rafBernoulliProbability p
        (Finset.univ : Finset (RepositoryChannel n))
        (repositoryCoreSupports n t) (repositorySupportRequirements n t) =
      ∑ config ∈ repositoryRAFFibreConfigurations n t,
        jointFibreBernoulliWeight p
          (Finset.univ : Finset (RepositoryChannel n)) config := by
  rw [rafBernoulliProbability_eq_sum_catalogue_weights]
  rw [repository_catalogue_eq_raf_configurations]

end OverlapCorrectedRAF.Source
