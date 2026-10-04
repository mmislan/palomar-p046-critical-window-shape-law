module

public import proofs.OverlapCorrectedRAF.Source.KauffmanRepositoryCRS
public import proofs.RAFReactionQuotient.ClosureProjection

@[expose] public section

namespace RAFReactionQuotient
open Classical RAF RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source

abbrev OrderedChannel (n : ℕ) :=
  {uv : Molecule n × Molecule n // molLength uv.1 + molLength uv.2 ≤ n}

def orderedCRS (n t : ℕ) : ReversibleCRS (Molecule n) (OrderedChannel n) where
  lhs r := {r.val.1, r.val.2}
  rhs r := {concatMolecule r.val.1 r.val.2 r.property}
  food := binaryFood n t

theorem precedes_total {n : ℕ} (u v : Molecule n) :
    moleculePrecedes u v ∨ moleculePrecedes v u := by
  unfold moleculePrecedes
  omega

def canonical {n : ℕ} (r : OrderedChannel n) : RepositoryChannel n :=
  if h : displayedConcat r.val.1 r.val.2 ≠ displayedConcat r.val.2 r.val.1 ∨
      moleculePrecedes r.val.1 r.val.2 then
    ⟨r.val, r.property, h⟩
  else
    ⟨(r.val.2, r.val.1), (Nat.add_comm (molLength r.val.2) (molLength r.val.1)).le.trans r.property,
      Or.inr ((precedes_total r.val.1 r.val.2).resolve_left (fun hp => h (Or.inr hp)))⟩

theorem molecule_ext {n : ℕ} {x y : Molecule n}
    (hl : molLength x = molLength y) (hc : x.2.val = y.2.val) : x = y := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  have hij : i = j := by apply Fin.ext; dsimp [molLength] at hl; omega
  subst j
  exact congrArg (Sigma.mk i) (Fin.ext hc)

theorem concat_code {n : ℕ} (u v : Molecule n)
    (h : molLength u + molLength v ≤ n) :
    (concatMolecule u v h).2.val = displayedConcat u v := by
  simp [concatMolecule, moleculeOfCode, concatCode, displayedConcat,
    finProdFinEquiv, Nat.add_comm, Nat.mul_comm]

theorem concat_comm_of_code {n : ℕ} (u v : Molecule n)
    (h : molLength u + molLength v ≤ n)
    (hc : displayedConcat u v = displayedConcat v u) :
    concatMolecule u v h = concatMolecule v u (by omega) := by
  apply molecule_ext
  · simp [concatMolecule, Nat.add_comm]
  · simpa only [concat_code] using hc

theorem canonical_lhs {n t : ℕ} (r : OrderedChannel n) :
    (repositoryCRS n t).lhs (canonical r) = (orderedCRS n t).lhs r := by
  unfold canonical
  split
  · rfl
  · simp [repositoryCRS, orderedCRS, Finset.pair_comm]

theorem canonical_rhs {n t : ℕ} (r : OrderedChannel n) :
    (repositoryCRS n t).rhs (canonical r) = (orderedCRS n t).rhs r := by
  unfold canonical
  split
  · rfl
  · rename_i h
    have hc : displayedConcat r.val.1 r.val.2 = displayedConcat r.val.2 r.val.1 := by
      by_contra hn
      exact h (Or.inl hn)
    simp only [repositoryCRS, orderedCRS]
    rw [concat_comm_of_code r.val.1 r.val.2 r.property hc]

theorem canonical_product_length {n : ℕ} (r : OrderedChannel n) :
    molLength (canonical r).val.1 + molLength (canonical r).val.2 =
      molLength r.val.1 + molLength r.val.2 := by
  unfold canonical
  split
  · rfl
  · exact Nat.add_comm _ _

theorem canonical_val_cases {n : ℕ} (r : OrderedChannel n) :
    (canonical r).val = r.val ∨ (canonical r).val = r.val.swap := by
  unfold canonical
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem canonical_surjective (n : ℕ) : Function.Surjective (@canonical n) := by
  intro j
  refine ⟨⟨j.val,j.property.1⟩, ?_⟩
  simp only [canonical, dite_eq_left j.property.2]

theorem canonical_fibre_le_two {n : ℕ} (j : RepositoryChannel n) :
    (Finset.univ.filter (fun r : OrderedChannel n => canonical r = j)).card ≤ 2 := by
  let a : OrderedChannel n := ⟨j.val,j.property.1⟩
  let b : OrderedChannel n := ⟨j.val.swap, by have := j.property.1; dsimp; omega⟩
  have hs : Finset.univ.filter (fun r : OrderedChannel n => canonical r = j) ⊆ {a,b} := by
    intro r hr
    have he := (Finset.mem_filter.mp hr).2
    have hv := canonical_val_cases r
    rw [he] at hv
    rcases hv with hv | hv
    · have : r = a := Subtype.ext hv.symm
      simp [this]
    · have : r = b := by
        apply Subtype.ext
        exact (congrArg Prod.swap hv).symm
      simp [this]
  exact (Finset.card_le_card hs).trans (by
    calc
      ({a,b} : Finset (OrderedChannel n)).card ≤ ({b} : Finset (OrderedChannel n)).card + 1 :=
        Finset.card_insert_le _ _
      _ = 2 := by simp)

theorem ordered_closure_eq_quotient {n : ℕ} (t : ℕ)
    (S : Finset (OrderedChannel n)) (k : ℕ) :
    revClosureAt (repositoryCRS n t) (S.image canonical) k =
      revClosureAt (orderedCRS n t) S k :=
  closureAt_image _ _ canonical canonical_lhs canonical_rhs rfl S k

theorem ordered_raf_iff_quotient {n : ℕ} (t : ℕ)
    (C : Catalysis (Molecule n) (OrderedChannel n)) :
    (∃ S, IsRevRAF (orderedCRS n t) C S) ↔
      ∃ T, IsRevRAF (repositoryCRS n t) (orCatalysis canonical C) T :=
  hasRAF_or_iff _ _ canonical canonical_lhs canonical_rhs rfl C

end RAFReactionQuotient
