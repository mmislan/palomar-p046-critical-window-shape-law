module

public import proofs.RAFReactionQuotient.QuotientMap

@[expose] public section

namespace RAFReactionQuotient
open Classical RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

def liftMolecule {n N : ℕ} (h : n ≤ N) (x : Molecule n) : Molecule N :=
  ⟨⟨x.1.val, lt_of_lt_of_le x.1.isLt h⟩, x.2⟩

@[simp] theorem liftMolecule_length {n N : ℕ} (h : n ≤ N) (x : Molecule n) :
    molLength (liftMolecule h x) = molLength x := rfl

def liftOrdered {n N : ℕ} (h : n ≤ N) (r : OrderedChannel n) : OrderedChannel N :=
  ⟨(liftMolecule h r.val.1, liftMolecule h r.val.2), r.property.trans h⟩

def liftQuotient {n N : ℕ} (h : n ≤ N) (j : RepositoryChannel n) : RepositoryChannel N :=
  ⟨(liftMolecule h j.val.1, liftMolecule h j.val.2), j.property.1.trans h, j.property.2⟩

theorem canonical_lift {n N : ℕ} (h : n ≤ N) (r : OrderedChannel n) :
    canonical (liftOrdered h r) = liftQuotient h (canonical r) := by
  unfold canonical
  have he :
      (displayedConcat (liftOrdered h r).val.1 (liftOrdered h r).val.2 ≠
        displayedConcat (liftOrdered h r).val.2 (liftOrdered h r).val.1 ∨
        moleculePrecedes (liftOrdered h r).val.1 (liftOrdered h r).val.2) ↔
      (displayedConcat r.val.1 r.val.2 ≠ displayedConcat r.val.2 r.val.1 ∨
        moleculePrecedes r.val.1 r.val.2) := Iff.rfl
  split <;> rename_i hc
  · rw [dite_eq_left (he.mp hc)]
    rfl
  · rw [dite_eq_right (fun hp => hc (he.mpr hp))]
    rfl

end RAFReactionQuotient
