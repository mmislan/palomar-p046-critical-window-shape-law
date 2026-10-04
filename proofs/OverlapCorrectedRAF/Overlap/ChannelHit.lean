module

public import proofs.OverlapCorrectedRAF.Core.OneCoreProbability

@[expose] public section

namespace OverlapCorrectedRAF.Overlap

open Polynomial

variable {M R J : Type*}

/-- Species overlap is overlap of eligible molecule sets. -/
def speciesOverlap [DecidableEq M] (W V : Finset M) : Finset M := W ∩ V

/-- Reaction-support overlap is logically distinct from species overlap. -/
def reactionOverlap [DecidableEq R] (C D : Finset R) : Finset R := C ∩ D

/-- Channel overlap is where dependence can occur in product catalysis. -/
def channelOverlap [DecidableEq J] (K L : Finset J) : Finset J := K ∩ L

/-- Catalytic-coordinate support retains both molecule and channel labels. -/
def catalyticCoordinateSupport [DecidableEq M] [DecidableEq J]
    (W : Finset M) (K : Finset J) : Finset (M × J) :=
  W.product K

/-- Union of a finite family of eligible molecule sets. -/
def familyUnion [DecidableEq M] (T : Finset (Finset M)) : Finset M :=
  T.biUnion id

/-- Polynomial form of the same exact local trace. -/
noncomputable def localHitPolynomial [DecidableEq M]
    (requirements : Finset (Finset M)) : Polynomial Int :=
  ∑ T ∈ requirements.powerset,
    C ((-1 : Int) ^ T.card) * X ^ (familyUnion T).card

/-- One channel's exact Bernoulli hit probability by inclusion--exclusion,
with `q=1-p`, obtained by evaluating its integer trace polynomial. -/
noncomputable def localHitProbability [DecidableEq M]
    (q : ℝ) (requirements : Finset (Finset M)) : ℝ :=
  eval q ((localHitPolynomial requirements).map (Int.castRingHom ℝ))

theorem localHitProbability_eq_eval [DecidableEq M]
    (q : ℝ) (requirements : Finset (Finset M)) :
    localHitProbability q requirements =
      eval q ((localHitPolynomial requirements).map (Int.castRingHom ℝ)) := rfl

/-- Independent channel fibres multiply after all within-channel overlap has
been retained by the local hit polynomial. -/
noncomputable def jointChannelHitProbability [DecidableEq M] [DecidableEq J]
    (q : ℝ) (channels : Finset J)
    (requirements : J → Finset (Finset M)) : ℝ :=
  ∏ j ∈ channels, localHitProbability q (requirements j)

theorem jointChannelHitProbability_exact [DecidableEq M] [DecidableEq J]
    (q : ℝ) (channels : Finset J)
    (requirements : J → Finset (Finset M)) :
    jointChannelHitProbability q channels requirements =
      ∏ j ∈ channels, localHitProbability q (requirements j) := rfl

/-- Equality of the channel-indexed local trace is sufficient for equality of
all joint Bernoulli weights. -/
theorem jointChannelHitProbability_congr_trace
    [DecidableEq M] [DecidableEq J]
    (q : ℝ) (channels : Finset J)
    (requirements requirements' : J → Finset (Finset M))
    (htrace : ∀ j ∈ channels,
      localHitPolynomial (requirements j) =
        localHitPolynomial (requirements' j)) :
    jointChannelHitProbability q channels requirements =
      jointChannelHitProbability q channels requirements' := by
  apply Finset.prod_congr rfl
  intro j hj
  rw [localHitProbability_eq_eval, localHitProbability_eq_eval, htrace j hj]

theorem localHitProbability_empty [DecidableEq M] (q : ℝ) :
    localHitProbability q (∅ : Finset (Finset M)) = 1 := by
  simp [localHitProbability, localHitPolynomial, familyUnion]

theorem localHitProbability_singleton [DecidableEq M]
    (q : ℝ) (W : Finset M) :
    localHitProbability q {W} = 1 - q ^ W.card := by
  have hpoly : localHitPolynomial {W} = 1 - X ^ W.card := by
    rw [localHitPolynomial]
    change (∑ T ∈ (insert W (∅ : Finset (Finset M))).powerset,
      C ((-1 : Int) ^ T.card) * X ^ (familyUnion T).card) = 1 - X ^ W.card
    rw [Finset.sum_powerset_insert (s := ∅) (a := W) (by simp)]
    simp [familyUnion]
    ring
  rw [localHitProbability, hpoly]
  simp

/-- Exact two-core correction on one shared channel. -/
theorem localHitProbability_pair [DecidableEq M]
    (q : ℝ) {W V : Finset M} (hWV : W ≠ V) :
    localHitProbability q {W, V} =
      1 - q ^ W.card - q ^ V.card + q ^ (W ∪ V).card := by
  have hsum : ∀ f : Finset (Finset M) → Polynomial Int,
      ∑ T ∈ ({V} : Finset (Finset M)).powerset, f T = f ∅ + f {V} := by
    intro f
    change (∑ T ∈ (insert V (∅ : Finset (Finset M))).powerset, f T) =
      f ∅ + f {V}
    rw [Finset.sum_powerset_insert (s := ∅) (a := V) (by simp)]
    simp
  have hpoly : localHitPolynomial {W, V} =
      1 - X ^ W.card - X ^ V.card + X ^ (W ∪ V).card := by
    rw [localHitPolynomial,
      Finset.sum_powerset_insert (s := {V}) (a := W) (by simp [hWV])]
    rw [hsum, hsum]
    simp [familyUnion, hWV]
    ring
  rw [localHitProbability, hpoly]
  simp

/-- Exact three-requirement inclusion--exclusion on one channel. -/
theorem localHitProbability_triple [DecidableEq M]
    (q : ℝ) {W V U : Finset M}
    (hWV : W ≠ V) (hWU : W ≠ U) (hVU : V ≠ U) :
    localHitProbability q {W, V, U} =
      1 - q ^ W.card - q ^ V.card - q ^ U.card +
      q ^ (W ∪ V).card + q ^ (W ∪ U).card + q ^ (V ∪ U).card -
      q ^ (W ∪ V ∪ U).card := by
  have hsingle : ∀ (A : Finset M) (f : Finset (Finset M) → Polynomial Int),
      ∑ T ∈ ({A} : Finset (Finset M)).powerset, f T = f ∅ + f {A} := by
    intro A f
    change (∑ T ∈ (insert A (∅ : Finset (Finset M))).powerset, f T) =
      f ∅ + f {A}
    rw [Finset.sum_powerset_insert (s := ∅) (a := A) (by simp)]
    simp
  have hpair : ∀ (A B : Finset M), A ≠ B →
      ∀ f : Finset (Finset M) → Polynomial Int,
        ∑ T ∈ ({A, B} : Finset (Finset M)).powerset, f T =
          f ∅ + f {A} + f {B} + f {A, B} := by
    intro A B hAB f
    rw [Finset.sum_powerset_insert (s := {B}) (a := A) (by simp [hAB])]
    rw [hsingle, hsingle]
    simp
    ring
  have hpoly : localHitPolynomial {W, V, U} =
      1 - X ^ W.card - X ^ V.card - X ^ U.card +
      X ^ (W ∪ V).card + X ^ (W ∪ U).card + X ^ (V ∪ U).card -
      X ^ (W ∪ V ∪ U).card := by
    rw [localHitPolynomial,
      Finset.sum_powerset_insert (s := {V, U}) (a := W) (by simp [hWV, hWU])]
    rw [hpair V U hVU, hpair V U hVU]
    simp [familyUnion, hWV, hWU, hVU]
    ring
  rw [localHitProbability, hpoly]
  simp

end OverlapCorrectedRAF.Overlap
