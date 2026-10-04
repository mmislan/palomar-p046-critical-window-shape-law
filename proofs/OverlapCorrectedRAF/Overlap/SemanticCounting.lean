module

public import proofs.OverlapCorrectedRAF.Overlap.FinitePartition
public import Mathlib.Combinatorics.Enumerative.InclusionExclusion
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace OverlapCorrectedRAF.Overlap

open Polynomial

/-- Actual molecule subsets in one channel fibre that miss `W`. -/
def fibreMissConfigurations
    {M : Type*} [Fintype M] [DecidableEq M] (W : Finset M) :
    Finset (Finset M) :=
  Finset.univ.filter fun A => Disjoint A W

/-- Actual molecule subsets in one channel fibre that hit every requested
eligible set. -/
def fibreHitConfigurations
    {M : Type*} [Fintype M] [DecidableEq M]
    (requirements : Finset (Finset M)) : Finset (Finset M) :=
  requirements.inf fun W => (fibreMissConfigurations W)ᶜ

theorem mem_fibreHitConfigurations_iff
    {M : Type*} [Fintype M] [DecidableEq M]
    {requirements : Finset (Finset M)} {A : Finset M} :
    A ∈ fibreHitConfigurations requirements ↔
      ∀ W ∈ requirements, ¬ Disjoint A W := by
  simp [fibreHitConfigurations, fibreMissConfigurations, Finset.mem_inf]

/-- Ordinary cardinality-generating polynomial of a finite family of subsets. -/
noncomputable def subsetCardPolynomial
    {M : Type*} [DecidableEq M] (configurations : Finset (Finset M)) :
    Polynomial Int :=
  ∑ A ∈ configurations, X ^ A.card

theorem subsetCardPolynomial_coeff
    {M : Type*} [DecidableEq M]
    (configurations : Finset (Finset M)) (Q : Nat) :
    (subsetCardPolynomial configurations).coeff Q =
      ((configurations.filter fun A => A.card = Q).card : Int) := by
  simp [subsetCardPolynomial, Polynomial.coeff_X_pow, eq_comm]

theorem subsetCardPolynomial_powerset
    {M : Type*} [DecidableEq M] (U : Finset M) :
    subsetCardPolynomial U.powerset = (X + 1) ^ U.card := by
  induction U using Finset.induction_on with
  | empty => simp [subsetCardPolynomial]
  | @insert a U ha ih =>
      have hsecond :
          (∑ A ∈ U.powerset, (X : Polynomial Int) ^ (insert a A).card) =
            X * ∑ A ∈ U.powerset, X ^ A.card := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro A hA
        have hnot : a ∉ A := fun haA =>
          ha (Finset.mem_powerset.mp hA haA)
        rw [Finset.card_insert_of_notMem hnot, pow_succ]
        ring
      rw [subsetCardPolynomial]
      change (∑ A ∈ (insert a U).powerset,
        (X : Polynomial Int) ^ A.card) = _
      rw [Finset.sum_powerset_insert (s := U) (a := a) ha]
      rw [hsecond]
      rw [← subsetCardPolynomial, ih, Finset.card_insert_of_notMem ha]
      ring

theorem inf_fibreMissConfigurations_eq_powerset_compl
    {M : Type*} [Fintype M] [DecidableEq M]
    (T : Finset (Finset M)) :
    T.inf fibreMissConfigurations = (familyUnion T)ᶜ.powerset := by
  ext A
  simp only [Finset.mem_inf, fibreMissConfigurations, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_powerset]
  simp only [familyUnion, Finset.disjoint_left, Finset.subset_iff,
    Finset.mem_compl, Finset.mem_biUnion, not_exists, not_and]
  constructor
  · intro h x hx W hW
    exact h W hW hx
  · intro h W hW x hx
    exact h hx W hW

/-- Semantic local theorem: the inclusion--exclusion polynomial is exactly
the ordinary generating polynomial of actual fibre subsets hitting every
required eligible set. -/
theorem localFixedQHitPolynomial_counts_configurations
    {M : Type*} [Fintype M] [DecidableEq M]
    (requirements : Finset (Finset M)) :
    subsetCardPolynomial (fibreHitConfigurations requirements) =
      localFixedQHitPolynomial requirements := by
  rw [subsetCardPolynomial, fibreHitConfigurations]
  rw [Finset.inclusion_exclusion_sum_inf_compl]
  rw [localFixedQHitPolynomial]
  apply Finset.sum_congr rfl
  intro T hT
  rw [inf_fibreMissConfigurations_eq_powerset_compl]
  rw [← subsetCardPolynomial, subsetCardPolynomial_powerset]
  rw [Finset.card_compl]
  exact Polynomial.smul_eq_C_mul ((-1 : Int) ^ T.card)

/-- Every coefficient of the local inclusion--exclusion polynomial is an
actual configuration count; in particular, no signed-to-natural conversion is
needed to interpret fixed-cardinality sampling. -/
theorem localFixedQHitPolynomial_coeff_counts
    {M : Type*} [Fintype M] [DecidableEq M]
    (requirements : Finset (Finset M)) (Q : Nat) :
    (localFixedQHitPolynomial requirements).coeff Q =
      (((fibreHitConfigurations requirements).filter fun A => A.card = Q).card : Int) := by
  rw [← localFixedQHitPolynomial_counts_configurations]
  exact subsetCardPolynomial_coeff _ _

/-- Bernoulli mass of one fibre subset, with every molecule-coordinate
independently present with probability `p`. -/
def fibreBernoulliWeight
    {M : Type*} [Fintype M] (p : ℝ) (A : Finset M) : ℝ :=
  p ^ A.card * (1 - p) ^ (Fintype.card M - A.card)

theorem sum_powerset_fibreBernoulliWeight
    {M : Type*} [Fintype M] [DecidableEq M]
    (p : ℝ) (U : Finset M) :
    (∑ A ∈ U.powerset, fibreBernoulliWeight p A) =
      (1 - p) ^ (Fintype.card M - U.card) := by
  classical
  have hUcard : U.card ≤ Fintype.card M := by
    simpa using Finset.card_le_card (show U ⊆ (Finset.univ : Finset M) by simp)
  have hbinomial :
      (∑ A ∈ U.powerset,
        p ^ A.card * (1 - p) ^ (U.card - A.card)) = 1 := by
    calc
      _ = ∑ A ∈ U.powerset,
          (∏ _x ∈ A, p) * ∏ _x ∈ U \ A, (1 - p) := by
            apply Finset.sum_congr rfl
            intro A hA
            simp only [Finset.prod_const]
            rw [Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hA)]
      _ = ∏ _x ∈ U, (p + (1 - p)) := by
            rw [Finset.prod_add]
      _ = 1 := by simp
  calc
    (∑ A ∈ U.powerset, fibreBernoulliWeight p A) =
        (1 - p) ^ (Fintype.card M - U.card) *
          ∑ A ∈ U.powerset,
            p ^ A.card * (1 - p) ^ (U.card - A.card) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A hA
      have hAcard : A.card ≤ U.card :=
        Finset.card_le_card (Finset.mem_powerset.mp hA)
      rw [fibreBernoulliWeight,
        show Fintype.card M - A.card =
          (Fintype.card M - U.card) + (U.card - A.card) by omega,
        pow_add]
      ring
    _ = _ := by rw [hbinomial, mul_one]

/-- The local inclusion--exclusion expression is the literal Bernoulli mass
of the actual hitting fibre subsets. -/
theorem localHitProbability_eq_sum_fibreBernoulliWeight
    {M : Type*} [Fintype M] [DecidableEq M]
    (p : ℝ) (requirements : Finset (Finset M)) :
    localHitProbability (1 - p) requirements =
      ∑ A ∈ fibreHitConfigurations requirements,
        fibreBernoulliWeight p A := by
  rw [fibreHitConfigurations]
  rw [Finset.inclusion_exclusion_sum_inf_compl]
  simp_rw [inf_fibreMissConfigurations_eq_powerset_compl]
  simp_rw [sum_powerset_fibreBernoulliWeight]
  simp only [Finset.card_compl]
  have hsub (T : Finset (Finset M)) :
      Fintype.card M - (Fintype.card M - (familyUnion T).card) =
        (familyUnion T).card := by
    have hcard : (familyUnion T).card ≤ Fintype.card M := by
      simpa using Finset.card_le_card
        (show familyUnion T ⊆ (Finset.univ : Finset M) by simp)
    omega
  simp_rw [hsub]
  simp only [localHitProbability, localHitPolynomial]
  rw [Polynomial.map_sum]
  change (Polynomial.evalRingHom (1 - p))
      (∑ T ∈ requirements.powerset,
        (C ((-1 : Int) ^ T.card) * X ^ (familyUnion T).card).map
          (Int.castRingHom ℝ)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro T hT
  simp

/-- Actual choices of a hitting molecule subset in every active channel
fibre.  The dependent function remembers only fibres indexed by `channels`. -/
noncomputable def jointFibreHitConfigurations
    {M J K : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq J] [DecidableEq K]
    (channels : Finset J) (requirements : K → J → Finset M)
    (selected : Finset K) :
    Finset (∀ j, j ∈ channels → Finset M) := by
  classical
  exact channels.pi fun j =>
    fibreHitConfigurations (selectedRequirementFamily selected requirements j)

theorem mem_jointFibreHitConfigurations_iff
    {M J K : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq J] [DecidableEq K]
    {channels : Finset J} {requirements : K → J → Finset M}
    {selected : Finset K} {config : ∀ j, j ∈ channels → Finset M} :
    config ∈ jointFibreHitConfigurations channels requirements selected ↔
      ∀ k ∈ selected,
        config ∈ jointFibreHitConfigurations channels requirements {k} := by
  classical
  simp only [jointFibreHitConfigurations, Finset.mem_pi,
    mem_fibreHitConfigurations_iff, selectedRequirementFamily,
    Finset.mem_image, Finset.mem_filter, Finset.mem_singleton]
  aesop

/-- Bernoulli mass of a dependent channel-fibre configuration. -/
def jointFibreBernoulliWeight
    {M J : Type*} [Fintype M]
    (p : ℝ) (channels : Finset J)
    (config : ∀ j, j ∈ channels → Finset M) : ℝ :=
  ∏ j ∈ channels.attach, fibreBernoulliWeight p (config j.1 j.2)

/-- Ordinary generating polynomial of actual channel-fibre choices, graded
by their total number of catalytic coordinates. -/
noncomputable def jointFibreCardPolynomial
    {M J K : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq J] [DecidableEq K]
    (channels : Finset J) (requirements : K → J → Finset M)
    (selected : Finset K) : Polynomial Int :=
  ∑ config ∈ jointFibreHitConfigurations channels requirements selected,
    X ^ ∑ j ∈ channels.attach, (config j.1 j.2).card

/-- Semantic global theorem: the product polynomial is exactly the ordinary
generating polynomial of actual independent channel-fibre configurations. -/
theorem jointFixedQHitPolynomial_counts_fibre_configurations
    {M J K : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq J] [DecidableEq K]
    (channels : Finset J) (requirements : K → J → Finset M)
    (selected : Finset K) :
    jointFibreCardPolynomial channels requirements selected =
      jointFixedQHitPolynomial channels requirements selected := by
  classical
  rw [jointFibreCardPolynomial, jointFibreHitConfigurations,
    jointFixedQHitPolynomial]
  simp_rw [← localFixedQHitPolynomial_counts_configurations]
  simp_rw [subsetCardPolynomial]
  rw [Finset.prod_sum]
  apply Finset.sum_congr rfl
  intro config hconfig
  rw [Finset.prod_pow_eq_pow_sum]

theorem jointBernoulliHitProbability_eq_sum_fibre_weights
    {M J K : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq J] [DecidableEq K]
    (p : ℝ) (channels : Finset J) (requirements : K → J → Finset M)
    (selected : Finset K) :
    jointBernoulliHitProbability p channels requirements selected =
      ∑ config ∈ jointFibreHitConfigurations channels requirements selected,
        jointFibreBernoulliWeight p channels config := by
  classical
  rw [jointBernoulliHitProbability, jointFibreHitConfigurations]
  simp_rw [localHitProbability_eq_sum_fibreBernoulliWeight]
  rw [Finset.prod_sum]
  rfl

theorem sum_jointFibreHitConfigurations_eq_jointFixedQHitPolynomial
    {M J K : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq J] [DecidableEq K]
    (channels : Finset J) (requirements : K → J → Finset M)
    (selected : Finset K) :
    (∑ config ∈ jointFibreHitConfigurations channels requirements selected,
      X ^ ∑ j ∈ channels.attach, (config j.1 j.2).card) =
        jointFixedQHitPolynomial channels requirements selected := by
  rw [← jointFibreCardPolynomial]
  exact jointFixedQHitPolynomial_counts_fibre_configurations _ _ _

theorem inf'_singletonCoreConfigurations_eq_selected
    {M J K : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq J] [DecidableEq K]
    (channels : Finset J) (requirements : K → J → Finset M)
    (selected : Finset K) (hselected : selected.Nonempty) :
    selected.inf' hselected (fun k =>
      jointFibreHitConfigurations channels requirements {k}) =
        jointFibreHitConfigurations channels requirements selected := by
  classical
  ext config
  rw [Finset.mem_inf' hselected]
  exact mem_jointFibreHitConfigurations_iff.symm

/-- Actual fibre configurations activating at least one indexed core. -/
noncomputable def catalogueFibreHitConfigurations
    {M J K : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq J] [DecidableEq K]
    (channels : Finset J) (cores : Finset K)
    (requirements : K → J → Finset M) :
    Finset (∀ j, j ∈ channels → Finset M) :=
  cores.biUnion fun k => jointFibreHitConfigurations channels requirements {k}

/-- Ordinary generating polynomial of the actual union of the indexed core
activation events. -/
noncomputable def catalogueFibreCardPolynomial
    {M J K : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq J] [DecidableEq K]
    (channels : Finset J) (cores : Finset K)
    (requirements : K → J → Finset M) : Polynomial Int :=
  ∑ config ∈ catalogueFibreHitConfigurations channels cores requirements,
    X ^ ∑ j ∈ channels.attach, (config j.1 j.2).card

/-- Semantic outer theorem: the core inclusion--exclusion polynomial is the
generating polynomial of the actual union of indexed activation events. -/
theorem rafFixedQCountPolynomial_counts_catalogue_configurations
    {M J K : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq J] [DecidableEq K]
    (channels : Finset J) (cores : Finset K)
    (requirements : K → J → Finset M) :
    catalogueFibreCardPolynomial channels cores requirements =
      rafFixedQCountPolynomial channels cores requirements := by
  classical
  rw [catalogueFibreCardPolynomial, catalogueFibreHitConfigurations,
    rafFixedQCountPolynomial]
  rw [Finset.inclusion_exclusion_sum_biUnion]
  simp_rw [inf'_singletonCoreConfigurations_eq_selected,
    sum_jointFibreHitConfigurations_eq_jointFixedQHitPolynomial]
  change (∑ selected : {s : Finset K //
      s ∈ cores.powerset.filter (·.Nonempty)},
    (-1 : Int) ^ (selected.1.card + 1) •
      jointFixedQHitPolynomial channels requirements selected.1) = _
  rw [← Finset.sum_subtype
    (p := fun selected => selected ∈ cores.powerset.filter (·.Nonempty))
    (cores.powerset.filter (·.Nonempty)) (fun _ => Iff.rfl)
    (fun selected => (-1 : Int) ^ (selected.card + 1) •
      jointFixedQHitPolynomial channels requirements selected)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro selected hselected
  by_cases hnonempty : selected.Nonempty
  · simp [hnonempty]
  · simp [hnonempty]

theorem rafBernoulliProbability_eq_sum_catalogue_weights
    {M J K : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq J] [DecidableEq K]
    (p : ℝ) (channels : Finset J) (cores : Finset K)
    (requirements : K → J → Finset M) :
    rafBernoulliProbability p channels cores requirements =
      ∑ config ∈ catalogueFibreHitConfigurations channels cores requirements,
        jointFibreBernoulliWeight p channels config := by
  classical
  symm
  rw [catalogueFibreHitConfigurations, rafBernoulliProbability]
  rw [Finset.inclusion_exclusion_sum_biUnion]
  simp_rw [inf'_singletonCoreConfigurations_eq_selected,
    ← jointBernoulliHitProbability_eq_sum_fibre_weights]
  change (∑ selected : {s : Finset K //
      s ∈ cores.powerset.filter (·.Nonempty)},
    (-1 : Int) ^ (selected.1.card + 1) •
      jointBernoulliHitProbability p channels requirements selected.1) = _
  rw [← Finset.sum_subtype
    (p := fun selected => selected ∈ cores.powerset.filter (·.Nonempty))
    (cores.powerset.filter (·.Nonempty)) (fun _ => Iff.rfl)
    (fun selected => (-1 : Int) ^ (selected.card + 1) •
      jointBernoulliHitProbability p channels requirements selected)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro selected hselected
  by_cases hnonempty : selected.Nonempty
  · simp [hnonempty]
  · simp [hnonempty]

theorem rafFixedQCountPolynomial_coeff_counts_catalogue
    {M J K : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq J] [DecidableEq K]
    (channels : Finset J) (cores : Finset K)
    (requirements : K → J → Finset M) (Q : Nat) :
    (rafFixedQCountPolynomial channels cores requirements).coeff Q =
      (((catalogueFibreHitConfigurations channels cores requirements).filter
        fun config =>
          (∑ j ∈ channels.attach, (config j.1 j.2).card) = Q).card : Int) := by
  rw [← rafFixedQCountPolynomial_counts_catalogue_configurations]
  simp [catalogueFibreCardPolynomial, Polynomial.coeff_X_pow, eq_comm]

/-- The old fixed-`Q` quotient has a literal event-cardinality numerator. -/
theorem rafFixedQProbability_eq_actual_catalogue_ratio
    {M J K : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq J] [DecidableEq K]
    (channels : Finset J) (cores : Finset K)
    (requirements : K → J → Finset M) (Q : Nat) :
    rafFixedQProbability channels cores requirements Q =
      ((catalogueFibreHitConfigurations channels cores requirements).filter
        fun config =>
          (∑ j ∈ channels.attach, (config j.1 j.2).card) = Q).card /
        Nat.choose (Fintype.card M * channels.card) Q := by
  rw [rafFixedQProbability,
    rafFixedQCountPolynomial_coeff_counts_catalogue]
  simp

end OverlapCorrectedRAF.Overlap
