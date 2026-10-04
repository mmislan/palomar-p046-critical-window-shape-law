module

public import proofs.RAF.Concrete.PolymerCRS
public import proofs.RAFCriticalWindowQuantitative.EffectiveSeed
public import proofs.HordijkSteelThreshold.InfiniteStaticLaw
public import proofs.RAFReactionQuotient.QuotientMap
public import proofs.RAFCriticalWindowQuantitative.GeometricCutoff

@[expose] public section

namespace P046SolutionSupport
open MeasureTheory RAF.Polymer RAF.Concrete HordijkSteelThreshold RAFReactionQuotient RAFCriticalWindowQuantitative

theorem reaction_length_add {n : Nat} (r : Reaction n) :
    reactionLeftLength r + reactionRightLength r = reactionProductLength r :=
  RAF.Concrete.reaction_length_add r

theorem reaction_left_pos {n : Nat} (r : Reaction n) : 1 ≤ reactionLeftLength r :=
  RAF.Concrete.reaction_left_pos r

theorem reaction_right_pos {n : Nat} (r : Reaction n) : 1 ≤ reactionRightLength r :=
  RAF.Concrete.reaction_right_pos r

theorem reaction_product_le {n : Nat} (r : Reaction n) : reactionProductLength r ≤ n :=
  RAF.Concrete.reaction_product_le r

theorem reaction_pow_split {n : Nat} (r : Reaction n) :
    2 ^ (r.1.val + 1) =
      2 ^ reactionLeftLength r * 2 ^ reactionRightLength r :=
  RAF.Concrete.reaction_pow_split r

theorem molLength_reactionLeft {n : Nat} (r : Reaction n) :
    molLength (reactionLeft r) = reactionLeftLength r :=
  RAF.Concrete.molLength_reactionLeft r

theorem molLength_reactionRight {n : Nat} (r : Reaction n) :
    molLength (reactionRight r) = reactionRightLength r :=
  RAF.Concrete.molLength_reactionRight r

theorem seedTest_exists (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1) (m : ℕ) :
    ∃ k, RAFCriticalWindowQuantitative.seedTest b m k :=
  RAFCriticalWindowQuantitative.seedTest_exists b hb hb1 m

theorem measurable_currySplitField : Measurable HordijkSteelThreshold.currySplitField :=
  HordijkSteelThreshold.measurable_currySplitField

theorem precedes_total {n : ℕ} (u v : Molecule n) :
    OverlapCorrectedRAF.Source.moleculePrecedes u v ∨
      OverlapCorrectedRAF.Source.moleculePrecedes v u :=
  RAFReactionQuotient.precedes_total u v

theorem geometricTest_exists (t c ε : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hε : 0 < ε) : ∃ r, RAFCriticalWindowQuantitative.geometricTest t c ε r :=
  RAFCriticalWindowQuantitative.geometricTest_exists t c ε ht0 ht1 hε

theorem repair_ratio (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (L : ℕ) :
    0 ≤ 1-q^(L+1) ∧ 1-q^(L+1) < 1 :=
  RAFCriticalWindowQuantitative.repair_ratio q hq hq1 L

end P046SolutionSupport
