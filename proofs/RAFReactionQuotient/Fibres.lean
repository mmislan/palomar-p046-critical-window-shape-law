module

public import proofs.RAFReactionQuotient.SplitAdapter
public import proofs.RAFReactionQuotient.CapCompatibility

@[expose] public section

namespace RAFReactionQuotient
open Classical RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

theorem splitToOrdered_injective (n : ℕ) : Function.Injective (@splitToOrdered n) := by
  intro r s he
  have hp : reactionProduct r = reactionProduct s := by
    rw [← split_concat r, ← split_concat s]
    exact congrArg (fun q : OrderedChannel n => concatMolecule q.val.1 q.val.2 q.property) he
  have hl : reactionLeftLength r = reactionLeftLength s := by
    simpa only [splitToOrdered, molLength_reactionLeft] using
      congrArg (fun q : OrderedChannel n => molLength q.val.1) he
  rcases r with ⟨ri, rw, rk⟩
  rcases s with ⟨si, sw, sk⟩
  have hi : ri = si := congrArg Sigma.fst hp
  subst si
  have hw : rw = sw := Fin.ext (congrArg (fun x : Molecule n => x.2.val) hp)
  subst sw
  have hk : rk = sk := by
    apply Fin.ext
    dsimp [reactionLeftLength] at hl
    omega
  subst sk
  rfl

theorem split_fibre_le_two {n : ℕ} (j : RepositoryChannel n) :
    (Finset.univ.filter (fun r : Reaction n => splitToQuotient r = j)).card ≤ 2 := by
  let S := Finset.univ.filter (fun r : Reaction n => splitToQuotient r = j)
  have hs : S.image splitToOrdered ⊆
      Finset.univ.filter (fun q : OrderedChannel n => canonical q = j) := by
    intro q hq
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2⟩
  calc
    S.card = (S.image splitToOrdered).card :=
      (Finset.card_image_of_injective S (splitToOrdered_injective n)).symm
    _ ≤ _ := Finset.card_le_card hs
    _ ≤ 2 := canonical_fibre_le_two j

end RAFReactionQuotient
