module

public import proofs.OverlapCorrectedRAF.Core.FiniteCoreEvent
public import proofs.RAF.Corrected.BoundaryEvents

@[expose] public section

namespace OverlapCorrectedRAF.Core

open RAF.Corrected RAF.Probability
open Polynomial

/-- Bernoulli weight of a core with `w` eligible molecules and `k` distinct
independent channels. -/
def oneCoreBernoulliProbability (p : ℝ) (w k : Nat) : ℝ :=
  atLeastOneProbability p w ^ k

theorem oneCoreBernoulliProbability_exact (p : ℝ) (w k : Nat) :
    oneCoreBernoulliProbability p w k =
      (1 - (1 - p) ^ w) ^ k := by
  simp [oneCoreBernoulliProbability, atLeastOneProbability,
    allAbsentProbability_eq_pow]

/-- The exact ordinary generating polynomial for fixed-`Q` configurations
activating one core.  Each of the `k` required channel fibres contributes a
nonempty subset of its `w` eligible coordinates; all remaining coordinates
are arbitrary. -/
noncomputable def oneCoreFixedQCountPolynomial
    (ambientMolecules ambientChannels w k : Nat) : Polynomial Int :=
  (((X + 1) ^ w - 1) ^ k) *
    (X + 1) ^ (ambientMolecules * ambientChannels - w * k)

/-- Exact number of size-`Q` configurations in the channel-fibre
decomposition.  `Int.toNat` is harmless because the displayed polynomial is a
product of subset-generating polynomials with nonnegative coefficients. -/
noncomputable def oneCoreFixedQCount
    (ambientMolecules ambientChannels w k Q : Nat) : Nat :=
  Int.toNat ((oneCoreFixedQCountPolynomial
    ambientMolecules ambientChannels w k).coeff Q)

/-- Uniform fixed-`Q` probability, with denominator the number of all
`Q`-subsets of the ambient molecule--channel coordinates. -/
noncomputable def oneCoreFixedQProbability
    (ambientMolecules ambientChannels w k Q : Nat) : ℝ :=
  oneCoreFixedQCount ambientMolecules ambientChannels w k Q /
    Nat.choose (ambientMolecules * ambientChannels) Q

theorem oneCoreFixedQProbability_exact
    (ambientMolecules ambientChannels w k Q : Nat) :
    oneCoreFixedQProbability ambientMolecules ambientChannels w k Q =
      Int.toNat ((oneCoreFixedQCountPolynomial
        ambientMolecules ambientChannels w k).coeff Q) /
        Nat.choose (ambientMolecules * ambientChannels) Q := by
  rfl

/-- Summing the fixed-`Q` numerator over `Q` gives the transparent count:
each required fibre has `2^w-1` choices and every outside coordinate is free. -/
theorem oneCoreFixedQCountPolynomial_eval_one
    (ambientMolecules ambientChannels w k : Nat) :
    (oneCoreFixedQCountPolynomial ambientMolecules ambientChannels w k).eval 1 =
      ((2 : Int) ^ w - 1) ^ k *
        2 ^ (ambientMolecules * ambientChannels - w * k) := by
  simp [oneCoreFixedQCountPolynomial]

/-- The one-channel factor has zero constant coefficient and binomial
coefficient `choose w q` in every positive degree. -/
theorem coeff_nonemptyFibrePolynomial (w q : Nat) :
    (((X + 1) ^ w - 1 : Polynomial Int).coeff q) =
      if q = 0 then 0 else Nat.choose w q := by
  by_cases hq : q = 0
  · subst q
    rw [coeff_sub, coeff_X_add_one_pow]
    simp
  · rw [coeff_sub, coeff_X_add_one_pow]
    rw [coeff_one]
    simp [hq]

end OverlapCorrectedRAF.Core
