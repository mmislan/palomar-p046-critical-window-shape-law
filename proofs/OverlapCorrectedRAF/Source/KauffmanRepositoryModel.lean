module

public import proofs.RAF.Concrete.PolymerCRS

@[expose] public section

namespace OverlapCorrectedRAF.Source

open RAF.Polymer RAF.Concrete

/-- The public repository orders molecules first by length and then by their
binary word code. -/
def moleculeRank {n : Nat} (x : Molecule n) : Nat :=
  (2 ^ molLength x - 2) + x.2.val

/-- The exact order used when `create_XFR` builds its molecule list: shorter
words precede longer words, and equal-length words use binary-code order. -/
abbrev moleculePrecedes {n : Nat} (u v : Molecule n) : Prop :=
  molLength u < molLength v ∨
    (molLength u = molLength v ∧ u.2.val ≤ v.2.val)

/-- Numeric code of the displayed concatenation `u ++ v`. -/
def displayedConcat {n : Nat} (u v : Molecule n) : Nat :=
  u.2.val * 2 ^ molLength v + v.2.val

/-- Canonical representative of the repository's displayed-reaction quotient.
Both orientations are retained when `u ++ v` and `v ++ u` differ.  When they
coincide, the repository emits only the orientation whose first factor occurs
first in its molecule list. -/
abbrev RepositoryChannel (n : Nat) :=
  {uv : Molecule n × Molecule n //
    molLength uv.1 + molLength uv.2 ≤ n ∧
      (displayedConcat uv.1 uv.2 ≠ displayedConcat uv.2 uv.1 ∨
        moleculePrecedes uv.1 uv.2)}

/-- A fixed-food source gateway, represented in the intrinsic food type.  For
`t = 2` and `n ≥ 4`, every such pair embeds as a repository channel. -/
abbrev RepositoryGateway (t : Nat) :=
  {uv : Molecule t × Molecule t //
    displayedConcat uv.1 uv.2 ≠ displayedConcat uv.2 uv.1 ∨
      moleculePrecedes uv.1 uv.2}

theorem card_repository_channels_three :
    Fintype.card (RepositoryChannel 3) = 18 := by decide

/-- Exact source gateway count.  This is `36 - 2`: among the 36 ordered pairs
of six food molecules, only `(A,AA)/(AA,A)` and `(B,BB)/(BB,B)` are distinct
ordered pairs with equal displayed concatenation, so each pair is collapsed
once by the repository. -/
theorem card_repository_gateway_binary_t2 :
    Fintype.card (RepositoryGateway 2) = 34 := by decide

end OverlapCorrectedRAF.Source
