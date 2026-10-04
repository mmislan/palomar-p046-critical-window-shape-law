module

public import proofs.RAFReactionQuotient.QuotientMap

@[expose] public section

namespace RAFReactionQuotient
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

/-- Fixing one nonempty factor and the other factor's length determines the
commuting word uniquely. Binary positional arithmetic avoids primitive roots. -/
theorem commuting_factor_unique {n : ℕ} (u v w : Molecule n)
    (hlen : molLength v = molLength w)
    (hv : displayedConcat u v = displayedConcat v u)
    (hw : displayedConcat u w = displayedConcat w u) : v = w := by
  apply molecule_ext hlen
  have hp : 1 < 2 ^ molLength u := by
    unfold molLength
    rw [pow_succ]
    have hh : 0 < 2 ^ u.1.val := by positivity
    omega
  unfold displayedConcat at hv hw
  rw [hlen] at hv
  nlinarith

theorem commuting_equal_length {n : ℕ} (u v : Molecule n)
    (hlen : molLength u = molLength v)
    (hv : displayedConcat u v = displayedConcat v u) : u = v := by
  exact (commuting_factor_unique u v u hlen.symm hv rfl).symm

theorem noncanonical_strict_lengths {n : ℕ} (r : OrderedChannel n)
    (h : ¬ (displayedConcat r.val.1 r.val.2 ≠ displayedConcat r.val.2 r.val.1 ∨
      moleculePrecedes r.val.1 r.val.2)) : molLength r.val.2 < molLength r.val.1 := by
  have hc : displayedConcat r.val.1 r.val.2 = displayedConcat r.val.2 r.val.1 :=
    Classical.byContradiction (fun hn => h (Or.inl hn))
  have hn : ¬ moleculePrecedes r.val.1 r.val.2 := fun hp => h (Or.inr hp)
  have he : molLength r.val.1 ≠ molLength r.val.2 := by
    intro he
    have hv := commuting_equal_length r.val.1 r.val.2 he hc
    apply hn
    rw [hv]
    exact Or.inr ⟨rfl,le_rfl⟩
  unfold moleculePrecedes at hn
  omega

end RAFReactionQuotient
