module

public import proofs.OverlapCorrectedRAF.Overlap.ChannelHit

@[expose] public section

namespace OverlapCorrectedRAF.Overlap

open Polynomial

/-- Ordinary generating polynomial for subsets of one molecule fibre which
hit every member of `requirements`.  Inclusion--exclusion removes subsets
missing each requested eligible set. -/
noncomputable def localFixedQHitPolynomial
    {M : Type*} [Fintype M] [DecidableEq M]
    (requirements : Finset (Finset M)) : Polynomial Int :=
  ∑ T ∈ requirements.powerset,
    C ((-1 : Int) ^ T.card) *
      (X + 1) ^ (Fintype.card M - (familyUnion T).card)

theorem localFixedQHitPolynomial_empty
    {M : Type*} [Fintype M] [DecidableEq M] :
    localFixedQHitPolynomial (∅ : Finset (Finset M)) =
      (X + 1) ^ Fintype.card M := by
  simp [localFixedQHitPolynomial, familyUnion]

theorem localFixedQHitPolynomial_singleton
    {M : Type*} [Fintype M] [DecidableEq M] (W : Finset M) :
    localFixedQHitPolynomial {W} =
      (X + 1) ^ Fintype.card M -
        (X + 1) ^ (Fintype.card M - W.card) := by
  rw [localFixedQHitPolynomial]
  change (∑ T ∈ (insert W (∅ : Finset (Finset M))).powerset,
    C ((-1 : Int) ^ T.card) *
      (X + 1) ^ (Fintype.card M - (familyUnion T).card)) = _
  rw [Finset.sum_powerset_insert (s := ∅) (a := W) (by simp)]
  simp [familyUnion]
  ring

/-- The distinct eligible sets requested on channel `j` by a selected family
of cores.  The empty set is the sentinel for a channel not used by that core. -/
def selectedRequirementFamily
    {M J K : Type*} [DecidableEq M] [DecidableEq K]
    (selected : Finset K) (requirements : K → J → Finset M) (j : J) :
    Finset (Finset M) :=
  (selected.filter fun k => (requirements k j).Nonempty).image
    fun k => requirements k j

/-- The exact size-generating polynomial for catalysis configurations making
every selected core active.  Channel fibres are disjoint, hence multiply. -/
noncomputable def jointFixedQHitPolynomial
    {M J K : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq J] [DecidableEq K]
    (channels : Finset J) (requirements : K → J → Finset M)
    (selected : Finset K) : Polynomial Int :=
  ∏ j ∈ channels,
    localFixedQHitPolynomial (selectedRequirementFamily selected requirements j)

theorem jointFixedQHitPolynomial_exact
    {M J K : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq J] [DecidableEq K]
    (channels : Finset J) (requirements : K → J → Finset M)
    (selected : Finset K) :
    jointFixedQHitPolynomial channels requirements selected =
      ∏ j ∈ channels,
        localFixedQHitPolynomial
          (selectedRequirementFamily selected requirements j) := by
  rfl

theorem jointFixedQHitPolynomial_empty
    {M J K : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq J] [DecidableEq K]
    (channels : Finset J) (requirements : K → J → Finset M) :
    jointFixedQHitPolynomial channels requirements (∅ : Finset K) =
      (X + 1) ^ (Fintype.card M * channels.card) := by
  simp [jointFixedQHitPolynomial, selectedRequirementFamily,
    localFixedQHitPolynomial_empty, pow_mul]

/-- Exact fixed-`Q` intersection weight for a selected family of cores. -/
noncomputable def jointFixedQHitCount
    {M J K : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq J] [DecidableEq K]
    (channels : Finset J) (requirements : K → J → Finset M)
    (selected : Finset K) (Q : Nat) : Int :=
  (jointFixedQHitPolynomial channels requirements selected).coeff Q

theorem jointFixedQHitCount_exact
    {M J K : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq J] [DecidableEq K]
    (channels : Finset J) (requirements : K → J → Finset M)
    (selected : Finset K) (Q : Nat) :
    jointFixedQHitCount channels requirements selected Q =
      (∏ j ∈ channels,
        localFixedQHitPolynomial
          (selectedRequirementFamily selected requirements j)).coeff Q := by
  rfl

/-- Inclusion--exclusion numerator polynomial for the union of all core
activation events.  The coefficient of degree `Q` is the exact signed count
of size-`Q` configurations activating at least one indexed core. -/
noncomputable def rafFixedQCountPolynomial
    {M J K : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq J] [DecidableEq K]
    (channels : Finset J) (cores : Finset K)
    (requirements : K → J → Finset M) : Polynomial Int :=
  ∑ selected ∈ cores.powerset,
    if selected.Nonempty then
      C ((-1 : Int) ^ (selected.card + 1)) *
        jointFixedQHitPolynomial channels requirements selected
    else 0

/-- Inclusion--exclusion numerator polynomial for configurations activating
no indexed core. -/
noncomputable def noRAFFixedQCountPolynomial
    {M J K : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq J] [DecidableEq K]
    (channels : Finset J) (cores : Finset K)
    (requirements : K → J → Finset M) : Polynomial Int :=
  ∑ selected ∈ cores.powerset,
    C ((-1 : Int) ^ selected.card) *
      jointFixedQHitPolynomial channels requirements selected

theorem rafFixedQCountPolynomial_exact
    {M J K : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq J] [DecidableEq K]
    (channels : Finset J) (cores : Finset K)
    (requirements : K → J → Finset M) :
    rafFixedQCountPolynomial channels cores requirements =
      ∑ selected ∈ cores.powerset,
        if selected.Nonempty then
          C ((-1 : Int) ^ (selected.card + 1)) *
            jointFixedQHitPolynomial channels requirements selected
        else 0 := by
  rfl

theorem noRAFFixedQCountPolynomial_exact
    {M J K : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq J] [DecidableEq K]
    (channels : Finset J) (cores : Finset K)
    (requirements : K → J → Finset M) :
    noRAFFixedQCountPolynomial channels cores requirements =
      ∑ selected ∈ cores.powerset,
        C ((-1 : Int) ^ selected.card) *
          jointFixedQHitPolynomial channels requirements selected := by
  rfl

noncomputable def rafFixedQProbability
    {M J K : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq J] [DecidableEq K]
    (channels : Finset J) (cores : Finset K)
    (requirements : K → J → Finset M) (Q : Nat) : ℝ :=
  Int.toNat ((rafFixedQCountPolynomial channels cores requirements).coeff Q) /
    Nat.choose (Fintype.card M * channels.card) Q

theorem rafFixedQProbability_exact
    {M J K : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq J] [DecidableEq K]
    (channels : Finset J) (cores : Finset K)
    (requirements : K → J → Finset M) (Q : Nat) :
    rafFixedQProbability channels cores requirements Q =
      Int.toNat ((∑ selected ∈ cores.powerset,
        if selected.Nonempty then
          C ((-1 : Int) ^ (selected.card + 1)) *
            jointFixedQHitPolynomial channels requirements selected
        else 0).coeff Q) /
        Nat.choose (Fintype.card M * channels.card) Q := by
  rfl

/-- Bernoulli intersection probability for a selected family of cores. -/
noncomputable def jointBernoulliHitProbability
    {M J K : Type*} [DecidableEq M] [DecidableEq J] [DecidableEq K]
    (p : ℝ) (channels : Finset J) (requirements : K → J → Finset M)
    (selected : Finset K) : ℝ :=
  ∏ j ∈ channels,
    localHitProbability (1 - p)
      (selectedRequirementFamily selected requirements j)

/-- Exact Bernoulli probability of at least one indexed core, with every
overlap retained by the inner channel traces and the outer core
inclusion--exclusion. -/
noncomputable def rafBernoulliProbability
    {M J K : Type*} [DecidableEq M] [DecidableEq J] [DecidableEq K]
    (p : ℝ) (channels : Finset J) (cores : Finset K)
    (requirements : K → J → Finset M) : ℝ :=
  ∑ selected ∈ cores.powerset,
    if selected.Nonempty then
      (-1 : ℝ) ^ (selected.card + 1) *
        jointBernoulliHitProbability p channels requirements selected
    else 0

noncomputable def noRAFBernoulliProbability
    {M J K : Type*} [DecidableEq M] [DecidableEq J] [DecidableEq K]
    (p : ℝ) (channels : Finset J) (cores : Finset K)
    (requirements : K → J → Finset M) : ℝ :=
  ∑ selected ∈ cores.powerset,
    (-1 : ℝ) ^ selected.card *
      jointBernoulliHitProbability p channels requirements selected

theorem rafBernoulliProbability_exact
    {M J K : Type*} [DecidableEq M] [DecidableEq J] [DecidableEq K]
    (p : ℝ) (channels : Finset J) (cores : Finset K)
    (requirements : K → J → Finset M) :
    rafBernoulliProbability p channels cores requirements =
      ∑ selected ∈ cores.powerset,
        if selected.Nonempty then
          (-1 : ℝ) ^ (selected.card + 1) *
            jointBernoulliHitProbability p channels requirements selected
        else 0 := by
  rfl

theorem noRAFBernoulliProbability_exact
    {M J K : Type*} [DecidableEq M] [DecidableEq J] [DecidableEq K]
    (p : ℝ) (channels : Finset J) (cores : Finset K)
    (requirements : K → J → Finset M) :
    noRAFBernoulliProbability p channels cores requirements =
      ∑ selected ∈ cores.powerset,
        (-1 : ℝ) ^ selected.card *
          jointBernoulliHitProbability p channels requirements selected := by
  rfl

/-- Pure inclusion--exclusion identity behind the nonoverlap specialization.
If every selected-core intersection factors into its one-core weights, the
exact RAF union reduces to the familiar independent-core product. -/
theorem independentCoreUnionExpansion
    {K : Type*} [DecidableEq K] (cores : Finset K) (weight : K → ℝ) :
    (∑ selected ∈ cores.powerset,
      if selected.Nonempty then
        (-1 : ℝ) ^ (selected.card + 1) * ∏ k ∈ selected, weight k
      else 0) =
      1 - ∏ k ∈ cores, (1 - weight k) := by
  have hno :
      (∑ selected ∈ cores.powerset,
        (-1 : ℝ) ^ selected.card * ∏ k ∈ selected, weight k) =
        ∏ k ∈ cores, (1 - weight k) := by
    rw [Finset.prod_sub]
    simp
  rw [← hno]
  rw [eq_sub_iff_add_eq]
  rw [← Finset.sum_add_distrib]
  calc
    _ = ((if (∅ : Finset K).Nonempty then
          (-1 : ℝ) ^ ((∅ : Finset K).card + 1) *
            ∏ k ∈ (∅ : Finset K), weight k else 0) +
          (-1 : ℝ) ^ (∅ : Finset K).card *
            ∏ k ∈ (∅ : Finset K), weight k) := by
      apply Finset.sum_eq_single ∅
      · intro selected hselected hne
        have hsnon : selected.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
        simp [hsnon, pow_succ]
      · simp
    _ = 1 := by simp

theorem rafBernoulliProbability_eq_independent_of_factorizes
    {M J K : Type*} [DecidableEq M] [DecidableEq J] [DecidableEq K]
    (p : ℝ) (channels : Finset J) (cores : Finset K)
    (requirements : K → J → Finset M)
    (hfactor : ∀ selected ∈ cores.powerset,
      jointBernoulliHitProbability p channels requirements selected =
        ∏ k ∈ selected,
          jointBernoulliHitProbability p channels requirements {k}) :
    rafBernoulliProbability p channels cores requirements =
      1 - ∏ k ∈ cores,
        (1 - jointBernoulliHitProbability p channels requirements {k}) := by
  rw [rafBernoulliProbability]
  calc
    _ = ∑ selected ∈ cores.powerset,
        if selected.Nonempty then
          (-1 : ℝ) ^ (selected.card + 1) *
            ∏ k ∈ selected,
              jointBernoulliHitProbability p channels requirements {k}
        else 0 := by
      apply Finset.sum_congr rfl
      intro selected hselected
      rw [hfactor selected hselected]
    _ = _ := independentCoreUnionExpansion cores fun k =>
      jointBernoulliHitProbability p channels requirements {k}

/-- Term-by-term recovery of the source nonoverlap expression.  The first
hypothesis is precisely the intersection-factorization consequence supplied
by coordinate-disjoint catalytic supports; the second identifies each
singleton term with its closure size and number of used channels. -/
theorem rafBernoulliProbability_eq_source_nonoverlap
    {M J K : Type*} [DecidableEq M] [DecidableEq J] [DecidableEq K]
    (p : ℝ) (channels : Finset J) (cores : Finset K)
    (requirements : K → J → Finset M) (closureSize channelCount : K → Nat)
    (hfactor : ∀ selected ∈ cores.powerset,
      jointBernoulliHitProbability p channels requirements selected =
        ∏ k ∈ selected,
          jointBernoulliHitProbability p channels requirements {k})
    (hsingle : ∀ k ∈ cores,
      jointBernoulliHitProbability p channels requirements {k} =
        OverlapCorrectedRAF.Core.oneCoreBernoulliProbability p
          (closureSize k) (channelCount k)) :
    rafBernoulliProbability p channels cores requirements =
      1 - ∏ k ∈ cores,
        (1 - (1 - (1 - p) ^ closureSize k) ^ channelCount k) := by
  rw [rafBernoulliProbability_eq_independent_of_factorizes
    p channels cores requirements hfactor]
  apply congrArg (fun x : ℝ => 1 - x)
  apply Finset.prod_congr rfl
  intro k hk
  rw [hsingle k hk]
  exact congrArg (fun x : ℝ => 1 - x)
    (OverlapCorrectedRAF.Core.oneCoreBernoulliProbability_exact
      p (closureSize k) (channelCount k))

end OverlapCorrectedRAF.Overlap
