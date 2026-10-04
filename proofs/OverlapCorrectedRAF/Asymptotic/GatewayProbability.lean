module

public import proofs.OverlapCorrectedRAF.Source.KauffmanRepositoryCRS
public import proofs.HordijkSteelThreshold.PolymerCounts
public import proofs.RAF.Corrected.BoundaryEvents

@[expose] public section

namespace OverlapCorrectedRAF.Asymptotic

open RAF.Polymer RAF.Corrected
open OverlapCorrectedRAF.Source

/-- Number of independent molecule--gateway-channel coordinates in the literal
repository convention with binary food horizon two. -/
def repositoryGatewayCoordinateCount (n : Nat) : Nat :=
  Fintype.card (Molecule n) * Fintype.card (RepositoryGateway 2)

theorem repositoryGatewayCoordinateCount_exact (n : Nat) :
    repositoryGatewayCoordinateCount n = (2 ^ (n + 1) - 2) * 34 := by
  rw [repositoryGatewayCoordinateCount,
    HordijkSteelThreshold.card_molecules_exact,
    card_repository_gateway_binary_t2]

/-- Product-Bernoulli probability that at least one source gateway coordinate
is present. -/
def repositoryGatewayOpenProbability (p : ℝ) (n : Nat) : ℝ :=
  atLeastOneProbability p (repositoryGatewayCoordinateCount n)

/-- Exact finite gateway union bound with the source-corrected constant 34. -/
theorem repositoryGatewayOpenProbability_le {p : ℝ} (hp : p ≤ 1) (n : Nat) :
    repositoryGatewayOpenProbability p n ≤
      ((2 ^ (n + 1) - 2) * 34 : Nat) * p := by
  rw [repositoryGatewayOpenProbability]
  simpa [repositoryGatewayCoordinateCount_exact] using
    atLeastOneProbability_le_mul hp (repositoryGatewayCoordinateCount n)

/-- Probability-level adapter: once RAF-event containment in seed-open is
translated into a numerical inequality, the literal 34-channel cap follows. -/
theorem rafProbability_le_repositoryGatewayCap
    {p rafProbability : ℝ} {n : Nat}
    (hcontain : rafProbability ≤ repositoryGatewayOpenProbability p n)
    (hp : p ≤ 1) :
    rafProbability ≤ ((2 ^ (n + 1) - 2) * 34 : Nat) * p :=
  hcontain.trans (repositoryGatewayOpenProbability_le hp n)

end OverlapCorrectedRAF.Asymptotic
