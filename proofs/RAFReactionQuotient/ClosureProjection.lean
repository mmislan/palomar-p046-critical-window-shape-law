module

public import proofs.RAF.Concrete.SeedGateway

@[expose] public section

namespace RAFReactionQuotient
open Classical RAF RAF.Concrete

variable {M R J : Type*} [DecidableEq M] [DecidableEq R] [DecidableEq J]

omit [DecidableEq R] in
/-- Identifying reaction descriptions with identical chemistry preserves every
finite stage of ordinary reversible closure. -/
theorem closureAt_image (Q : ReversibleCRS M R) (P : ReversibleCRS M J)
    (π : R → J) (hl : ∀ r, P.lhs (π r) = Q.lhs r)
    (hr : ∀ r, P.rhs (π r) = Q.rhs r) (hf : P.food = Q.food)
    (S : Finset R) (k : ℕ) :
    revClosureAt P (S.image π) k = revClosureAt Q S k := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    simp only [revClosureAt, ih, revClosureStep]
    congr 1
    ext x
    simp [Finset.mem_biUnion, RevEnabledLhs, RevEnabledRhs, hl, hr]

def orCatalysis (π : R → J) (C : Catalysis M R) : Catalysis M J :=
  fun x j => ∃ r, π r = j ∧ C x r

omit [DecidableEq R] in
/-- Projection of a RAF retains its catalytic witnesses. -/
theorem raf_image (Q : ReversibleCRS M R) (P : ReversibleCRS M J)
    (π : R → J) (hl : ∀ r, P.lhs (π r) = Q.lhs r)
    (hr : ∀ r, P.rhs (π r) = Q.rhs r) (hf : P.food = Q.food)
    (C : Catalysis M R) (S : Finset R) (hS : IsRevRAF Q C S) :
    IsRevRAF P (orCatalysis π C) (S.image π) := by
  refine ⟨hS.1.image π, ?_, ?_⟩
  · intro j hj
    obtain ⟨r, hmem, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨k, hk⟩ := hS.2.1 r hmem
    exact ⟨k, by simpa only [hl, hr, closureAt_image Q P π hl hr hf] using hk⟩
  · intro j hj
    obtain ⟨r, hmem, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨x, k, hx, hc⟩ := hS.2.2 r hmem
    exact ⟨x, k, by rwa [closureAt_image Q P π hl hr hf], r, rfl, hc⟩

/-- Representatives are chosen using catalytic witnesses, not fixed in advance.
No independence assumption is needed for the deterministic OR equivalence. -/
theorem hasRAF_or_iff (Q : ReversibleCRS M R) (P : ReversibleCRS M J)
    (π : R → J) (hl : ∀ r, P.lhs (π r) = Q.lhs r)
    (hr : ∀ r, P.rhs (π r) = Q.rhs r) (hf : P.food = Q.food)
    (C : Catalysis M R) :
    (∃ S, IsRevRAF Q C S) ↔ ∃ T, IsRevRAF P (orCatalysis π C) T := by
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨S.image π, raf_image Q P π hl hr hf C S hS⟩
  · rintro ⟨T, hT⟩
    have hw (j : T) : ∃ r x k, π r = j.val ∧
        x ∈ revClosureAt P T k ∧ C x r := by
      obtain ⟨x, k, hx, r, he, hc⟩ := hT.2.2 j.val j.property
      exact ⟨r, x, k, he, hx, hc⟩
    choose rep cat stage hrep hcat hC using hw
    let S := T.attach.image rep
    have himage : S.image π = T := by
      ext j
      simp only [S, Finset.mem_image, Finset.mem_attach, true_and]
      constructor
      · rintro ⟨r, ⟨i, rfl⟩, rfl⟩
        rw [hrep i]
        exact i.property
      · intro hj
        exact ⟨rep ⟨j,hj⟩, ⟨⟨j,hj⟩, rfl⟩, hrep ⟨j,hj⟩⟩
    have hcl (k : ℕ) : revClosureAt Q S k = revClosureAt P T k := by
      rw [← himage, closureAt_image Q P π hl hr hf]
    refine ⟨S, ?_, ?_, ?_⟩
    · obtain ⟨j, hj⟩ := hT.1
      exact ⟨rep ⟨j,hj⟩, Finset.mem_image.mpr ⟨⟨j,hj⟩, Finset.mem_attach _ _, rfl⟩⟩
    · intro r hmem
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hmem
      obtain ⟨k, hk⟩ := hT.2.1 j.val j.property
      refine ⟨k, ?_⟩
      rw [hcl, ← hl, ← hr, hrep]
      exact hk
    · intro r hmem
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hmem
      exact ⟨cat j, stage j, by rw [hcl]; exact hcat j, hC j⟩

end RAFReactionQuotient
