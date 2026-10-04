module

public import proofs.OverlapCorrectedRAF.Source.ActualGatewayDock

@[expose] public section

namespace OverlapCorrectedRAF.Asymptotic

open RAF.Polymer
open OverlapCorrectedRAF.Overlap OverlapCorrectedRAF.Source

/-- The residual RAF mass after dividing out the necessary gateway event.
This is an algebraic conditional factor; it is defined only through the two
exact finite probabilities and does not assert probabilistic independence. -/
noncomputable def repositoryGatewayConditionedBulkProbability
    (p : ℝ) (n : Nat) : ℝ :=
  rafBernoulliProbability p Finset.univ
      (repositoryCoreSupports n 2) (repositorySupportRequirements n 2) /
    repositoryGatewayOpenProbability p n

/-- Exact boundary--bulk factorization whenever the gateway has nonzero
probability.  All unresolved large-system behavior is isolated in the second
factor. -/
theorem repositoryRAFBernoulliProbability_gateway_factorization
    {p : ℝ} {n : Nat} (hgateway : repositoryGatewayOpenProbability p n ≠ 0) :
    rafBernoulliProbability p Finset.univ
        (repositoryCoreSupports n 2) (repositorySupportRequirements n 2) =
      repositoryGatewayOpenProbability p n *
        repositoryGatewayConditionedBulkProbability p n := by
  rw [repositoryGatewayConditionedBulkProbability]
  calc
    _ = (rafBernoulliProbability p Finset.univ
          (repositoryCoreSupports n 2) (repositorySupportRequirements n 2) /
          repositoryGatewayOpenProbability p n) *
        repositoryGatewayOpenProbability p n :=
      (div_mul_cancel₀ _ hgateway).symm
    _ = _ := mul_comm _ _

end OverlapCorrectedRAF.Asymptotic
