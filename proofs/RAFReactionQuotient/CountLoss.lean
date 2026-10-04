module

public import proofs.RAFReactionQuotient.CommutingUniqueness
public import proofs.RAFReactionQuotient.Surjectivity
public import proofs.HordijkSteelThreshold.PolymerCounts

@[expose] public section

namespace RAFReactionQuotient
open Classical RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

abbrev IsCanonical {n : ℕ} (r : OrderedChannel n) : Prop :=
  displayedConcat r.val.1 r.val.2 ≠ displayedConcat r.val.2 r.val.1 ∨
    moleculePrecedes r.val.1 r.val.2

abbrev DeletedChannel (n : ℕ) := {r : OrderedChannel n // ¬ IsCanonical r}

theorem deleted_short_bound {n : ℕ} (r : DeletedChannel n) :
    molLength r.val.val.2 ≤ (n-1)/2 := by
  have hs := noncanonical_strict_lengths r.val r.property
  have hn := r.val.property
  omega

def deletedShort {n : ℕ} (r : DeletedChannel n) : Molecule ((n-1)/2) :=
  ⟨⟨r.val.val.2.1.val, by have := deleted_short_bound r; dsimp [molLength] at this; omega⟩,
    r.val.val.2.2⟩

def deletedKey {n : ℕ} (r : DeletedChannel n) : Molecule ((n-1)/2) × Fin n :=
  (deletedShort r, ⟨r.val.val.1.1.val,r.val.val.1.1.isLt⟩)

theorem deletedKey_injective (n : ℕ) : Function.Injective (@deletedKey n) := by
  intro r s he
  have hs : r.val.val.2 = s.val.val.2 := by
    apply molecule_ext
    · exact congrArg (fun z : Molecule ((n-1)/2) × Fin n => molLength z.1) he
    · exact congrArg (fun z : Molecule ((n-1)/2) × Fin n => z.1.2.val) he
  have hl : molLength r.val.val.1 = molLength s.val.val.1 := by
    have hh := congrArg (fun z : Molecule ((n-1)/2) × Fin n => z.2.val) he
    change r.val.val.1.1.val = s.val.val.1.1.val at hh
    unfold molLength
    omega
  have hc (t : DeletedChannel n) :
      displayedConcat t.val.val.2 t.val.val.1 = displayedConcat t.val.val.1 t.val.val.2 := by
    by_contra hn
    exact t.property (Or.inl (Ne.symm hn))
  have hv := commuting_factor_unique r.val.val.2 r.val.val.1 s.val.val.1 hl (hc r)
    (by rw [hs]; exact hc s)
  exact Subtype.ext (Subtype.ext (Prod.ext hv hs))

/-- A coarser-than-exact loss estimate sufficient for source normalization. -/
theorem deleted_card_bound (n : ℕ) :
    Fintype.card (DeletedChannel n) ≤ n*(2^((n-1)/2+1)-2) := by
  have hi := Fintype.card_le_of_injective (@deletedKey n) (deletedKey_injective n)
  simpa only [Fintype.card_prod,Fintype.card_fin,HordijkSteelThreshold.card_molecules_exact,
    Nat.mul_comm] using hi

def canonicalSubtypeEquiv (n : ℕ) : {r : OrderedChannel n // IsCanonical r} ≃
    RepositoryChannel n where
  toFun r := ⟨r.val.val,r.val.property,r.property⟩
  invFun j := ⟨⟨j.val,j.property.1⟩,j.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem ordered_card_eq_split (n : ℕ) :
    Fintype.card (OrderedChannel n) = Fintype.card (Reaction n) :=
  (Fintype.card_congr (Equiv.ofBijective (@splitToOrdered n)
    ⟨splitToOrdered_injective n,splitToOrdered_surjective n⟩)).symm

theorem deleted_card_eq_loss (n : ℕ) :
    Fintype.card (DeletedChannel n) =
      Fintype.card (Reaction n)-Fintype.card (RepositoryChannel n) := by
  rw [Fintype.card_subtype_compl,ordered_card_eq_split,
    Fintype.card_congr (canonicalSubtypeEquiv n)]

theorem split_count_le_quotient_add_loss_bound (n : ℕ) :
    Fintype.card (Reaction n) ≤ Fintype.card (RepositoryChannel n) +
      n*(2^((n-1)/2+1)-2) := by
  have hle : Fintype.card (RepositoryChannel n) ≤ Fintype.card (Reaction n) :=
    Fintype.card_le_of_surjective _ (splitToQuotient_surjective n)
  have hb := deleted_card_bound n
  rw [deleted_card_eq_loss] at hb
  omega

end RAFReactionQuotient
