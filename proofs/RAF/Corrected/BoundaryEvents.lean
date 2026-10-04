module

public import proofs.RAF.Probability.UniformCatalysis

@[expose] public section

namespace RAF.Corrected

open Filter RAF.Probability

/-- Probability of at least one success among `N` independent Bernoulli
coordinates, expressed through the already verified product model. -/
def atLeastOneProbability (p : ℝ) (N : Nat) : ℝ :=
  1 - allAbsentProbability p N

/-- Finite-coordinate union bound.  In particular it applies to the fixed
food-molecule × seed-reaction coordinates that create trivial one-reaction
RAFs. -/
theorem atLeastOneProbability_le_mul {p : ℝ} (hp : p ≤ 1) (N : Nat) :
    atLeastOneProbability p N ≤ N * p := by
  rw [atLeastOneProbability, allAbsentProbability_eq_pow]
  have h := one_add_mul_le_pow (a := -p) (by linarith : -2 ≤ -p) N
  have h' : 1 - (N : ℝ) * p ≤ (1 - p) ^ N := by
    convert h using 1
    ring
  linarith

/-- Every fixed family of exceptional coordinates disappears when its
individual catalysis probability tends to zero. -/
theorem finite_exception_tendsto_zero {p : Nat → ℝ} (N : Nat)
    (hp : Tendsto p atTop (nhds 0)) :
    Tendsto (fun n => atLeastOneProbability (p n) N) atTop (nhds 0) := by
  have hsub : Tendsto (fun n => 1 - p n) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hp
  have hpow : Tendsto (fun n => (1 - p n) ^ N) atTop (nhds ((1 - 0) ^ N)) :=
    hsub.pow N
  have hfinal : Tendsto (fun n => 1 - (1 - p n) ^ N) atTop
      (nhds (1 - (1 - 0) ^ N)) := tendsto_const_nhds.sub hpow
  simpa [atLeastOneProbability, allAbsentProbability_eq_pow] using hfinal

end RAF.Corrected
