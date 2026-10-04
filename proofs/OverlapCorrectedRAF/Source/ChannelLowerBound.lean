module

public import proofs.OverlapCorrectedRAF.Source.KauffmanRepositoryModel

@[expose] public section

namespace OverlapCorrectedRAF.Source

open RAF.Polymer RAF.Concrete

/-- Product words of length exactly `n`, split strictly before their midpoint.
Every such split is already the canonical representative of its repository
channel, including in the commuting case. -/
abbrev ShortLeftData (n : Nat) :=
  Σ a : Fin ((n - 1) / 2),
    Word (a.val + 1) × Word (n - (a.val + 1))

def shortLeftMolecules {n : Nat} (hn : 3 ≤ n)
    (d : ShortLeftData n) : Molecule n × Molecule n :=
  let leftLength := d.1.val + 1
  let rightLength := n - leftLength
  have hleft : leftLength ≤ n := by
    have ha := d.1.isLt
    omega
  have hrightPos : 1 ≤ rightLength := by
    have ha := d.1.isLt
    omega
  have hright : rightLength ≤ n := Nat.sub_le _ _
  (moleculeOfCode (by omega) hleft d.2.1,
    moleculeOfCode hrightPos hright d.2.2)

def shortLeftChannel {n : Nat} (hn : 3 ≤ n) :
    ShortLeftData n → RepositoryChannel n := fun d => by
  let uv := shortLeftMolecules hn d
  refine ⟨uv, ?_⟩
  have ha := d.1.isLt
  have hlen : molLength uv.1 < molLength uv.2 := by
    simp [uv, shortLeftMolecules]
    omega
  constructor
  · simp [uv, shortLeftMolecules]
    omega
  · exact Or.inr (Or.inl hlen)

theorem shortLeftChannel_injective {n : Nat} (hn : 3 ≤ n) :
    Function.Injective (shortLeftChannel hn) := by
  intro a b hab
  have hp := congrArg (fun z : RepositoryChannel n => z.1) hab
  have hl := congrArg (fun z : Molecule n × Molecule n => z.1) hp
  have hr := congrArg (fun z : Molecule n × Molecule n => z.2) hp
  have hlen := congrArg molLength hl
  have ha : a.1 = b.1 := by
    apply Fin.ext
    simpa [shortLeftChannel, shortLeftMolecules] using hlen
  rcases a with ⟨ai, ad⟩
  rcases b with ⟨bi, bd⟩
  change ai = bi at ha
  subst bi
  have had : ad = bd := by
    apply Prod.ext
    · apply Fin.ext
      simpa [shortLeftChannel, shortLeftMolecules, moleculeOfCode] using
        congrArg (fun z : Molecule n => z.2.val) hl
    · apply Fin.ext
      simpa [shortLeftChannel, shortLeftMolecules, moleculeOfCode] using
        congrArg (fun z : Molecule n => z.2.val) hr
  exact congrArg (fun d => Sigma.mk ai d) had

/-- A direct source-specific channel lower bound, prior to simplifying the
cardinality of `ShortLeftData`. -/
theorem shortLeft_card_le_repositoryChannels {n : Nat} (hn : 3 ≤ n) :
    Fintype.card (ShortLeftData n) ≤ Fintype.card (RepositoryChannel n) :=
  Fintype.card_le_of_injective (shortLeftChannel hn)
    (shortLeftChannel_injective hn)

theorem card_shortLeftData {n : Nat} (hn : 3 ≤ n) :
    Fintype.card (ShortLeftData n) = ((n - 1) / 2) * 2 ^ n := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  calc
    (∑ a : Fin ((n - 1) / 2), 2 ^ (a.val + 1) * 2 ^ (n - (a.val + 1))) =
        ∑ _a : Fin ((n - 1) / 2), 2 ^ n := by
      apply Finset.univ.sum_congr rfl
      intro a _ha
      rw [← pow_add]
      congr 1
      have ha := a.isLt
      omega
    _ = ((n - 1) / 2) * 2 ^ n := by simp

/-- Explicit `n 2^n` lower bound for the literal source channel type. -/
theorem repositoryChannel_card_lower {n : Nat} (hn : 3 ≤ n) :
    ((n - 1) / 2) * 2 ^ n ≤ Fintype.card (RepositoryChannel n) := by
  rw [← card_shortLeftData hn]
  exact shortLeft_card_le_repositoryChannels hn

end OverlapCorrectedRAF.Source
