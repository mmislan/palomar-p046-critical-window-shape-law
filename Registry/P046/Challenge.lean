module
public import Mathlib
@[expose] public section
/-!
P046: certified rational evaluation, sparse all-powers bounds, intensity flatness,
conditional finite-source comparison, productive histories and weak split example.
This independent statement imports Mathlib only. All project definitions are inline.
Theorem holes are intentional Challenge obligations; this file is not a Solution.
The sharp 10^-629 probability interpretation uses conventional census semantics
beyond checked coefficient arithmetic and is outside this selected formal endpoint.
Food is X_min(n,2); binaryFood n L is X_min(n,L), including L>n.
No profile, convergence-rate, desired-bound or rich-initial-food oracle is assumed.
-/
namespace HordijkSteelThreshold
end HordijkSteelThreshold
namespace OverlapCorrectedRAF.Asymptotic
end OverlapCorrectedRAF.Asymptotic
namespace OverlapCorrectedRAF.Source
end OverlapCorrectedRAF.Source
namespace RAF
end RAF
namespace RAF.Concrete
end RAF.Concrete
namespace RAF.Polymer
end RAF.Polymer
namespace RAFCriticalWindowQuantitative
end RAFCriticalWindowQuantitative
namespace RAFEmergenceApprox.Generic
end RAFEmergenceApprox.Generic
namespace RAFReactionQuotient
end RAFReactionQuotient

/- Definition slice: RAF/Polymer/Words.lean -/
section
namespace RAF.Polymer
/-- Binary words of exactly the given length, encoded by integers below 2^length. -/
abbrev Word (length : Nat) := Fin (2 ^ length)
/-- Nonempty binary words of length at most n; the first index represents length k+1. -/
abbrev Molecule (n : Nat) := Σ k : Fin n, Word (k.val + 1)
end RAF.Polymer
end

/- Definition slice: RAF/Polymer/Reactions.lean -/
section
namespace RAF.Polymer
/-- A product word and an interior split position, with one channel for both directions. -/
abbrev Reaction (n : Nat) := Σ k : Fin n, Word (k.val + 1) × Fin k.val
end RAF.Polymer
end

/- Definition slice: RAF/Concrete/PolymerCRS.lean -/
section
namespace RAF.Concrete
open RAF.Polymer
/-- The positive word length of an ambient molecule. -/
def molLength {n : Nat} (x : Molecule n) : Nat := x.1.val + 1
theorem moleculeOfCode_index_lt {n L : Nat} (hL : 1 ≤ L) (hLn : L ≤ n) :
    L - 1 < n :=
  Nat.lt_of_lt_of_le (Nat.sub_lt hL (Nat.zero_lt_succ 0)) hLn

theorem moleculeOfCode_pow_eq {L : Nat} (hL : 1 ≤ L) :
    2 ^ L = 2 ^ (L - 1 + 1) :=
  congrArg (fun k : Nat => 2 ^ k) (Nat.sub_add_cancel hL).symm

/-- Embed a positive length-indexed binary code in the cap-n molecule universe. -/
def moleculeOfCode {n L : Nat} (hL : 1 ≤ L) (hLn : L ≤ n)
    (x : Word L) : Molecule n :=
  ⟨⟨L - 1, moleculeOfCode_index_lt hL hLn⟩,
    Fin.cast (moleculeOfCode_pow_eq hL) x⟩
/-- Mixed-radix concatenation of two binary codes, preserving their total length. -/
def concatCode {n : Nat} (u v : Molecule n) : Word (molLength u + molLength v) :=
  Fin.cast ((pow_add 2 (molLength u) (molLength v)).symm)
    (finProdFinEquiv (u.2, v.2))
/-- The cap-n concatenated molecule, requiring its total length to fit the cap. -/
def concatMolecule {n : Nat} (u v : Molecule n)
    (h : molLength u + molLength v ≤ n) : Molecule n :=
  moleculeOfCode (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le u.1.val))
    (Nat.le_add_right (molLength u) (molLength v))) h (concatCode u v)
/-- Length of the product of a split-position channel. -/
def reactionProductLength {n : Nat} (r : Reaction n) : Nat := r.1.val + 1
/-- The interior split position, equal to the left factor length. -/
def reactionLeftLength {n : Nat} (r : Reaction n) : Nat := r.2.2.val + 1
/-- The product length minus the left factor length. -/
def reactionRightLength {n : Nat} (r : Reaction n) : Nat :=
  r.1.val - r.2.2.val
/-- Supporting proof obligation; its proof is not imported into this Challenge. -/
theorem reaction_length_add {n : Nat} (r : Reaction n) :
    reactionLeftLength r + reactionRightLength r = reactionProductLength r := by sorry
/-- Supporting proof obligation; its proof is not imported into this Challenge. -/
theorem reaction_left_pos {n : Nat} (r : Reaction n) :
    1 ≤ reactionLeftLength r := by sorry
/-- Supporting proof obligation; its proof is not imported into this Challenge. -/
theorem reaction_right_pos {n : Nat} (r : Reaction n) :
    1 ≤ reactionRightLength r := by sorry
/-- Supporting proof obligation; its proof is not imported into this Challenge. -/
theorem reaction_product_le {n : Nat} (r : Reaction n) :
    reactionProductLength r ≤ n := by sorry
/-- Supporting proof obligation; its proof is not imported into this Challenge. -/
theorem reaction_pow_split {n : Nat} (r : Reaction n) :
    2 ^ (r.1.val + 1) =
      2 ^ reactionLeftLength r * 2 ^ reactionRightLength r := by sorry
/-- The two binary factor codes obtained by inverting mixed-radix concatenation. -/
def splitCodes {n : Nat} (r : Reaction n) :
    Word (reactionLeftLength r) × Word (reactionRightLength r) :=
  (finProdFinEquiv).symm
    (Fin.cast (reaction_pow_split r) r.2.1)
/-- The left molecule of a split-position channel. -/
def reactionLeft {n : Nat} (r : Reaction n) : Molecule n :=
  moleculeOfCode (reaction_left_pos r)
    (by linarith [reaction_product_le r, reaction_length_add r]) (splitCodes r).1
/-- The right molecule of a split-position channel. -/
def reactionRight {n : Nat} (r : Reaction n) : Molecule n :=
  moleculeOfCode (reaction_right_pos r)
    (by linarith [reaction_product_le r, reaction_length_add r]) (splitCodes r).2
/-- The product molecule of a split-position channel. -/
def reactionProduct {n : Nat} (r : Reaction n) : Molecule n :=
  ⟨r.1, r.2.1⟩
/-- Supporting proof obligation; its proof is not imported into this Challenge. -/
@[simp] theorem molLength_reactionLeft {n : Nat} (r : Reaction n) :
    molLength (reactionLeft r) = reactionLeftLength r := by sorry
/-- Supporting proof obligation; its proof is not imported into this Challenge. -/
@[simp] theorem molLength_reactionRight {n : Nat} (r : Reaction n) :
    molLength (reactionRight r) = reactionRightLength r := by sorry
/-- Set-valued reactants, products and food for a reversible reaction system. -/
structure ReversibleCRS (M R : Type*) [DecidableEq M] where
  lhs : R → Finset M
  rhs : R → Finset M
  food : Finset M
/-- All reactant types are available; equal factors need only one type. -/
def RevEnabledLhs {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (available : Finset M) (r : R) : Prop :=
  Q.lhs r ⊆ available
/-- All product types are available, enabling reversible cleavage. -/
def RevEnabledRhs {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (available : Finset M) (r : R) : Prop :=
  Q.rhs r ⊆ available
/-- The stated decidability/probability instance for the preceding concrete definition. -/
instance revEnabledLhsDecidable {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (available : Finset M) (r : R) :
    Decidable (RevEnabledLhs Q available r) := by
  unfold RevEnabledLhs
  infer_instance
/-- The stated decidability/probability instance for the preceding concrete definition. -/
instance revEnabledRhsDecidable {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (available : Finset M) (r : R) :
    Decidable (RevEnabledRhs Q available r) := by
  unfold RevEnabledRhs
  infer_instance
/-- Adjoin products of enabled ligations and factors of enabled cleavages. -/
def revClosureStep {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) (available : Finset M) : Finset M :=
  available ∪ S.biUnion (fun r =>
    (if RevEnabledLhs Q available r then Q.rhs r else ∅) ∪
    (if RevEnabledRhs Q available r then Q.lhs r else ∅))
/-- Iterate reversible set closure from food for the specified number of rounds. -/
def revClosureAt {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) : Nat → Finset M
  | 0 => Q.food
  | k + 1 => revClosureStep Q S (revClosureAt Q S k)
/-- X_min(n,t): all ambient positive-length words of length at most t, even when t>n. -/
def binaryFood (n t : Nat) : Finset (Molecule n) :=
  Finset.univ.filter (fun x => molLength x ≤ t)
/-- Literal split-position reversible binary polymers with food X_min(n,t). -/
def binaryPolymerCRS (n t : Nat) : ReversibleCRS (Molecule n) (Reaction n) where
  lhs := fun r => {reactionLeft r, reactionRight r}
  rhs := fun r => {reactionProduct r}
  food := binaryFood n t
end RAF.Concrete
end

/- Definition slice: RAF/Core/CRS.lean -/
section
namespace RAF
/-- A catalyst relation on molecule and reversible-channel identities. -/
def Catalysis (M R : Type*) := M → R → Prop
end RAF
end

/- Definition slice: RAF/Concrete/SeedGateway.lean -/
section
namespace RAF.Concrete
open RAF RAF.Polymer
variable {M R : Type*} [DecidableEq M]
/-- A channel enabled in either orientation using the food types alone. -/
def RevSeedReaction (Q : ReversibleCRS M R) (r : R) : Prop :=
  Q.lhs r ⊆ Q.food ∨ Q.rhs r ⊆ Q.food
/-- The stated decidability/probability instance for the preceding concrete definition. -/
instance revSeedReactionDecidable (Q : ReversibleCRS M R) (r : R) :
    Decidable (RevSeedReaction Q r) := by
  unfold RevSeedReaction
  infer_instance
/-- Every selected channel endpoint is in a finite stage of its own food closure. -/
def RevFoodGenerated (Q : ReversibleCRS M R) (S : Finset R) : Prop :=
  ∀ r ∈ S, ∃ k, Q.lhs r ∪ Q.rhs r ⊆ revClosureAt Q S k
/-- Each selected channel has a marked catalyst in its own finite food closure. -/
def RevReflexivelyAutocatalytic (Q : ReversibleCRS M R)
    (C : Catalysis M R) (S : Finset R) : Prop :=
  ∀ r ∈ S, ∃ x k, x ∈ revClosureAt Q S k ∧ C x r
/-- A nonempty, food-generated, reflexively autocatalytic reversible channel subset. -/
def IsRevRAF (Q : ReversibleCRS M R) (C : Catalysis M R)
    (S : Finset R) : Prop :=
  S.Nonempty ∧ RevFoodGenerated Q S ∧ RevReflexivelyAutocatalytic Q C S
/-- Split channels enabled directly from cap-n food X_min(n,t). -/
abbrev PolymerSeedReaction (n t : Nat) :=
  {r : Reaction n // RevSeedReaction (binaryPolymerCRS n t) r}
end RAF.Concrete
end

/- Definition slice: RAF/Concrete/UniformModel.lean -/
section
namespace RAF.Concrete
open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer
/-- Independent molecule/channel coordinates for food-enabled split channels. -/
abbrev SeedCoord (n : Nat) := Molecule n × PolymerSeedReaction n 2
/-- The remaining split channels, outside the food-enabled channel class. -/
abbrev NonseedReaction (n : Nat) :=
  {r : Reaction n // ¬ RevSeedReaction (binaryPolymerCRS n 2) r}
/-- Independent molecule/channel coordinates for the remaining split channels. -/
abbrev NonseedCoord (n : Nat) := Molecule n × NonseedReaction n
/-- Catalytic subsets on two disjoint coordinate classes partitioning all split pairs. -/
abbrev CatalysisSample (n : Nat) := Set (SeedCoord n) × Set (NonseedCoord n)
/-- Intensity conversion lambda*n/card(Reaction n), prior to clamping. -/
noncomputable def rawCatalysisP (n : Nat) (lambda : ℝ) : ℝ :=
  lambda * n / Fintype.card (Reaction n)
/-- Clamp the source catalytic coordinate probability to [0,1], including small caps. -/
noncomputable def catalysisP (n : Nat) (lambda : ℝ) : I :=
  ⟨min 1 (max 0 (rawCatalysisP n lambda)), by
    constructor
    · exact le_min (by norm_num) (le_max_left _ _)
    · exact min_le_left _ _⟩
/-- Independent Bernoulli marks on both disjoint classes of catalytic coordinates. -/
noncomputable def uniformCatalysisMeasure (n : Nat) (lambda : ℝ) :
    Measure (CatalysisSample n) :=
  (setBernoulli (Set.univ : Set (SeedCoord n)) (catalysisP n lambda)).prod
    (setBernoulli (Set.univ : Set (NonseedCoord n)) (catalysisP n lambda))
/-- The stated decidability/probability instance for the preceding concrete definition. -/
noncomputable instance uniformCatalysisMeasure_isProbability (n : Nat) (lambda : ℝ) :
    IsProbabilityMeasure (uniformCatalysisMeasure n lambda) := by
  unfold uniformCatalysisMeasure
  infer_instance
/-- Reassemble the marked catalytic relation from its two disjoint coordinate subsets. -/
def catalysisOf {n : Nat} (ω : CatalysisSample n) :
    Catalysis (Molecule n) (Reaction n) := fun x r =>
  if h : RevSeedReaction (binaryPolymerCRS n 2) r then
    (x, ⟨r, h⟩) ∈ ω.1
  else
    (x, ⟨r, h⟩) ∈ ω.2
end RAF.Concrete
end

/- Definition slice: RAF/Concrete/Events.lean -/
section
namespace RAF.Concrete
open MeasureTheory ProbabilityTheory
open RAF RAF.Polymer
/-- Existence of an actual nonempty split RAF, allowing food and product catalysts. -/
def HasRAFEvent (n : Nat) : Set (CatalysisSample n) :=
  {ω | ∃ S : Finset (Reaction n),
    IsRevRAF (binaryPolymerCRS n 2) (catalysisOf ω) S}
end RAF.Concrete
end

/- Definition slice: HordijkSteelThreshold/AmbientIndependence.lean -/
section
namespace HordijkSteelThreshold
open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer
/-- Bernoulli(a) on Prop: mass a at True and 1-a at False. -/
noncomputable def ambientCoordLaw (p : I) : Measure Prop :=
  toNNReal p • Measure.dirac True + toNNReal (σ p) • Measure.dirac False
/-- The stated decidability/probability instance for the preceding concrete definition. -/
noncomputable instance ambientCoordLaw_isProbability (p : I) :
    IsProbabilityMeasure (ambientCoordLaw p) := by
  constructor
  simp [ambientCoordLaw]
end HordijkSteelThreshold
end

/- Definition slice: HordijkSteelThreshold/InfiniteLigation.lean -/
section
namespace HordijkSteelThreshold
/-- A Boolean-proposition mark on every product-word/split-position coordinate. -/
abbrev InfiniteSplitEnvironment := List Bool → Nat → Prop
end HordijkSteelThreshold
end

/- Definition slice: HordijkSteelThreshold/TemporaryReactionClosure.lean -/
section
namespace HordijkSteelThreshold
open Classical RAF.Polymer RAF.Concrete
/-- All cap-n molecules reached at some finite reversible split-closure stage. -/
noncomputable def temporaryReactionClosure {N : ℕ} (L : ℕ) (S : Finset (Reaction N)) :
    Finset (Molecule N) := Finset.univ.filter (fun x => ∃ k,
      x ∈ revClosureAt (binaryPolymerCRS N L) S k)
end HordijkSteelThreshold
end

/- Definition slice: RAFCriticalWindowQuantitative/FiniteClosure.lean -/
section
namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAF.Polymer RAF.Concrete
/-- The executable split closure after card(Molecule N) reversible rounds. -/
def computedClosure (N L : ℕ) (S : Finset (Reaction N)) : Finset (Molecule N) :=
  revClosureAt (binaryPolymerCRS N L) S (Fintype.card (Molecule N))
end RAFCriticalWindowQuantitative
end

/- Definition slice: HordijkSteelThreshold/WordMoleculeContourCount.lean -/
section
namespace HordijkSteelThreshold
open Classical
/-- The inherited explicit contour constant Cstar=2*7^64*81. -/
def molecularContourConstant : ℕ := 2 * 7 ^ 64 * 81
end HordijkSteelThreshold
end

/- Definition slice: RAFCriticalWindowQuantitative/EffectiveSeed.lean -/
section
namespace RAFCriticalWindowQuantitative
open Filter HordijkSteelThreshold
open scoped Topology
/-- Positive-index rational geometric deficit test Cstar*(1-b^2)^k*(m*(m+1)+1)<=1. -/
def seedTest (b : ℚ) (m k : ℕ) : Prop :=
  0 < k ∧ (molecularContourConstant : ℚ) * (1 - b^2)^k *
    ((m : ℚ) * (m+1) + 1) ≤ 1
/-- The stated decidability/probability instance for the preceding concrete definition. -/
instance (b : ℚ) (m k : ℕ) : Decidable (seedTest b m k) :=
  inferInstanceAs (Decidable (_ ∧ _))
/-- Supporting proof obligation; its proof is not imported into this Challenge. -/
theorem seedTest_exists (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1) (m : ℕ) :
    ∃ k, seedTest b m k := by sorry
/-- The least positive seed index satisfying seedTest, using its geometric existence proof. -/
def seedIndex (b : ℚ) (hb : 0 < b) (hb1 : b ≤ 1) (m : ℕ) : ℕ :=
  Nat.find (seedTest_exists b hb hb1 m)
end RAFCriticalWindowQuantitative
end

/- Definition slice: RAFCriticalWindowQuantitative/SeedDeficit.lean -/
section
namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold unitInterval
open scoped ENNReal
/-- Embed a valid rational probability in the real unit interval without changing its value. -/
def rationalParameter (b : ℚ) (hb : 0 ≤ b) (hb1 : b ≤ 1) : I :=
  ⟨b, by constructor <;> exact_mod_cast ‹_›⟩
end RAFCriticalWindowQuantitative
end

/- Definition slice: RAFCriticalWindowQuantitative/FiniteEventProbability.lean -/
section
namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold MeasureTheory unitInterval
open scoped ENNReal
/-- Exact finite Boolean event sum of products of q and 1-q, in rational arithmetic. -/
def rationalEventProbability (J : Type*) [Fintype J] [DecidableEq J] (q : ℚ)
    (event : (J → Bool) → Bool) : ℚ :=
  ∑ ω : J → Bool, if event ω then ∏ j, if ω j then q else 1-q else 0
end RAFCriticalWindowQuantitative
end

/- Definition slice: HordijkSteelThreshold/ReversibleFiniteCertificates.lean -/
section
namespace HordijkSteelThreshold
/-- Finite food/ligation/cleavage derivations in the marked infinite field. -/
inductive InfiniteReversibleGenerated (L : ℕ) (field : InfiniteSplitEnvironment) :
    List Bool → Prop
  | food {w} (hne : w ≠ []) (hL : w.length ≤ L) :
      InfiniteReversibleGenerated L field w
  | ligate {u v} (hu : InfiniteReversibleGenerated L field u)
      (hv : InfiniteReversibleGenerated L field v) (ho : field (u ++ v) u.length) :
      InfiniteReversibleGenerated L field (u ++ v)
  | left {u v} (hu : u ≠ []) (hv : v ≠ [])
      (hp : InfiniteReversibleGenerated L field (u ++ v))
      (ho : field (u ++ v) u.length) : InfiniteReversibleGenerated L field u
  | right {u v} (hu : u ≠ []) (hv : v ≠ [])
      (hp : InfiniteReversibleGenerated L field (u ++ v))
      (ho : field (u ++ v) u.length) : InfiniteReversibleGenerated L field v
end HordijkSteelThreshold
end

/- Definition slice: HordijkSteelThreshold/UnboundedTrialExtraction.lean -/
section
namespace HordijkSteelThreshold
open Classical
/-- For every length bound, some longer word has a finite reversible derivation. -/
def ReversibleUnbounded (L : ℕ) (field : InfiniteSplitEnvironment) : Prop :=
  ∀ K : ℕ, ∃ w, K < w.length ∧ InfiniteReversibleGenerated L field w
end HordijkSteelThreshold
end

/- Definition slice: HordijkSteelThreshold/InfiniteStaticLaw.lean -/
section
namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval
/-- View independent pair-indexed marks as a curried infinite split environment. -/
def currySplitField (ω : (List Bool × ℕ) → Prop) : InfiniteSplitEnvironment :=
  fun w k => ω (w,k)
/-- Supporting proof obligation; its proof is not imported into this Challenge. -/
theorem measurable_currySplitField : Measurable currySplitField := by sorry
/-- Independent Bernoulli marks on the countable latent product/split coordinates. -/
noncomputable def infiniteSplitPi (a : I) : Measure ((List Bool × ℕ) → Prop) :=
  Measure.infinitePi (fun _ => ambientCoordLaw a)
/-- The iid split-field law transported through the concrete currying map. -/
noncomputable def infiniteStaticMeasure (a : I) : Measure InfiniteSplitEnvironment :=
  (infiniteSplitPi a).map currySplitField
/-- The stated decidability/probability instance for the preceding concrete definition. -/
noncomputable instance infiniteSplitPi_probability (a : I) : IsProbabilityMeasure (infiniteSplitPi a) := by
  unfold infiniteSplitPi
  infer_instance
/-- The stated decidability/probability instance for the preceding concrete definition. -/
noncomputable instance infiniteStaticMeasure_probability (a : I) : IsProbabilityMeasure (infiniteStaticMeasure a) :=
  (Measure.isProbabilityMeasure_map_iff measurable_currySplitField.aemeasurable).2 inferInstance
end HordijkSteelThreshold
end

/- Definition slice: HordijkSteelThreshold/SplitPrefixIndependence.lean -/
section
namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal
/-- Pair-indexed latent coordinates for the infinite split and quotient laws. -/
abbrev SplitField := (List Bool × ℕ) → Prop
end HordijkSteelThreshold
end

/- Definition slice: RAFCriticalWindowQuantitative/RecordIteration.lean -/
section
namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold MeasureTheory unitInterval
open scoped ENNReal
/-- D_0=2 and D_(j+1)=2*D_j+ell; a raw escape-length cap. -/
def recordCap (ell : ℕ) : ℕ → ℕ :=
  Nat.rec 2 (fun _ cap => 2*cap+ell)
end RAFCriticalWindowQuantitative
end

/- Definition slice: HordijkSteelThreshold/SprinkledSeedLowerBound.lean -/
section
namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory unitInterval Filter
open scoped ENNReal
/-- Probability of unbounded food-generated split closure under the actual iid field. -/
noncomputable def staticSurvival (a : I) : ENNReal :=
  infiniteStaticMeasure a {field | ReversibleUnbounded 2 field}
end HordijkSteelThreshold
end

/- Definition slice: RAFCriticalWindowQuantitative/ExplicitTruncation.lean -/
section
namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold MeasureTheory unitInterval RAF.Polymer
open scoped ENNReal
/-- Probability of an infinite food-generated word longer than the raw length K. -/
noncomputable def splitEscapeProbability (a : I) (K : ℕ) : ENNReal :=
  infiniteSplitPi a {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w}
end RAFCriticalWindowQuantitative
end

/- Definition slice: RAFReactionQuotient/InfiniteSource.lean -/
section
namespace RAFReactionQuotient
open Classical MeasureTheory unitInterval HordijkSteelThreshold
/-- Collapse only valid commuting splits to the shorter-left canonical latent coordinate. -/
def canonicalIndex (z : List Bool × ℕ) : List Bool × ℕ :=
  if 0 < z.2 ∧ z.2 < z.1.length ∧ z.1.length-z.2 < z.2 ∧
      z.1.take z.2 ++ z.1.drop z.2 = z.1.drop z.2 ++ z.1.take z.2 then
    (z.1,z.1.length-z.2)
  else z
/-- Use a single iid latent mark for each canonical commuting-quotient coordinate. -/
def quotientField (ω : SplitField) : InfiniteSplitEnvironment :=
  fun w k => ω (canonicalIndex (w,k))
/-- Probability of unbounded food-generated closure in the canonical quotient field. -/
noncomputable def quotientSurvival (a : I) : ENNReal :=
  infiniteSplitPi a {ω | ReversibleUnbounded 2 (quotientField ω)}
end RAFReactionQuotient
end

/- Definition slice: RAFEmergenceApprox/GenericHistory.lean -/
section
namespace RAFEmergenceApprox.Generic
open Classical MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold
open RAF.Concrete
variable {X R : Type*} [Fintype X] [Fintype R]
/-- Independent catalytic marks for all molecule types in one quotient-channel column. -/
noncomputable def colLaw (X : Type*) [Fintype X] (p : I) : Measure (X → Prop) :=
  Measure.pi (fun _ : X => ambientCoordLaw p)
/-- The stated decidability/probability instance for the preceding concrete definition. -/
instance colLaw_probability (p : I) : IsProbabilityMeasure (colLaw X p) := by
  unfold colLaw
  infer_instance
/-- Independent channel columns, hence iid molecule/channel catalytic coordinates. -/
noncomputable def law (p : R → I) : Measure (R → X → Prop) :=
  Measure.pi (fun r => colLaw X (p r))
/-- The stated decidability/probability instance for the preceding concrete definition. -/
instance law_probability (p : R → I) : IsProbabilityMeasure (law (X := X) p) := by
  unfold law
  infer_instance
end RAFEmergenceApprox.Generic
end

/- Definition slice: OverlapCorrectedRAF/Source/KauffmanRepositoryModel.lean -/
section
namespace OverlapCorrectedRAF.Source
open RAF.Polymer RAF.Concrete
/-- Shortlex non-strict order used to choose the canonical commuting factor pair. -/
abbrev moleculePrecedes {n : Nat} (u v : Molecule n) : Prop :=
  molLength u < molLength v ∨
    (molLength u = molLength v ∧ u.2.val ≤ v.2.val)
/-- The integer code of uv in the displayed most-significant-factor convention. -/
def displayedConcat {n : Nat} (u v : Molecule n) : Nat :=
  u.2.val * 2 ^ molLength v + v.2.val
/-- Ordered factors fitting the cap; collapse swaps only when their products commute. -/
abbrev RepositoryChannel (n : Nat) :=
  {uv : Molecule n × Molecule n //
    molLength uv.1 + molLength uv.2 ≤ n ∧
      (displayedConcat uv.1 uv.2 ≠ displayedConcat uv.2 uv.1 ∨
        moleculePrecedes uv.1 uv.2)}
end OverlapCorrectedRAF.Source
end

/- Definition slice: OverlapCorrectedRAF/Source/KauffmanRepositoryCRS.lean -/
section
namespace OverlapCorrectedRAF.Source
open RAF RAF.Polymer RAF.Concrete
/-- Literal commuting-factor quotient channels with reversible endpoints and clipped food. -/
def repositoryCRS (n t : Nat) :
    ReversibleCRS (Molecule n) (RepositoryChannel n) where
  lhs := fun r => {r.1.1, r.1.2}
  rhs := fun r => {concatMolecule r.1.1 r.1.2 r.2.1}
  food := binaryFood n t
end OverlapCorrectedRAF.Source
end

/- Definition slice: RAFReactionQuotient/QuotientMap.lean -/
section
namespace RAFReactionQuotient
open Classical RAF RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
/-- Every ordered factor pair fitting the ambient cap, before quotienting commuting swaps. -/
abbrev OrderedChannel (n : ℕ) :=
  {uv : Molecule n × Molecule n // molLength uv.1 + molLength uv.2 ≤ n}
/-- Supporting proof obligation; its proof is not imported into this Challenge. -/
theorem precedes_total {n : ℕ} (u v : Molecule n) :
    moleculePrecedes u v ∨ moleculePrecedes v u := by sorry
/-- Choose the shortlex-ordered factors only for commuting products; retain other orientations. -/
def canonical {n : ℕ} (r : OrderedChannel n) : RepositoryChannel n :=
  if h : displayedConcat r.val.1 r.val.2 ≠ displayedConcat r.val.2 r.val.1 ∨
      moleculePrecedes r.val.1 r.val.2 then
    ⟨r.val, r.property, h⟩
  else
    ⟨(r.val.2, r.val.1), (Nat.add_comm (molLength r.val.2) (molLength r.val.1)).le.trans r.property,
      Or.inr ((precedes_total r.val.1 r.val.2).resolve_left (fun hp => h (Or.inr hp)))⟩
end RAFReactionQuotient
end

/- Definition slice: RAFReactionQuotient/History.lean -/
section
namespace RAFReactionQuotient
open Classical MeasureTheory ProbabilityTheory unitInterval
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source HordijkSteelThreshold
/-- All cap-n molecules reached at some finite reversible quotient-closure stage. -/
noncomputable def quotientClosure (n L : ℕ) (S : Finset (RepositoryChannel n)) :
    Finset (Molecule n) := Finset.univ.filter
      (fun x => ∃ k, x ∈ revClosureAt (repositoryCRS n L) S k)
/-- The direct iid catalytic law on actual quotient-channel identities. -/
noncomputable def quotientCatalyticLaw (n : ℕ) (p : I) :=
  RAFEmergenceApprox.Generic.law (X := Molecule n) (fun _ : RepositoryChannel n => p)
end RAFReactionQuotient
end

/- Definition slice: RAFReactionQuotient/SplitAdapter.lean -/
section
namespace RAFReactionQuotient
open Classical RAF RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
/-- Convert a split-position channel to its two ordered factors. -/
def splitToOrdered {n : ℕ} (r : Reaction n) : OrderedChannel n :=
  ⟨(reactionLeft r, reactionRight r), by
    simp only [molLength_reactionLeft, molLength_reactionRight, reaction_length_add]
    exact Nat.succ_le_of_lt r.1.isLt⟩
/-- The finite split-to-commuting-quotient coordinate map. -/
def splitToQuotient {n : ℕ} (r : Reaction n) : RepositoryChannel n :=
  canonical (splitToOrdered r)
end RAFReactionQuotient
end

/- Definition slice: RAFCriticalWindowQuantitative/QuotientExplicitTruncation.lean -/
section
namespace RAFCriticalWindowQuantitative
open Classical RAFReactionQuotient HordijkSteelThreshold MeasureTheory unitInterval RAF.Polymer
open scoped ENNReal
/-- Raw infinite escape probability in the canonical quotient field, with original food. -/
noncomputable def quotientEscapeProbability (a : I) (K : ℕ) : ENNReal :=
  infiniteSplitPi a {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (quotientField ω) w}
end RAFCriticalWindowQuantitative
end

/- Definition slice: HordijkSteelThreshold/NearFullPoolAsymptotics.lean -/
section
namespace HordijkSteelThreshold
open Classical Filter MeasureTheory RAF.Polymer RAF.Concrete unitInterval
open scoped Topology
/-- Retained pool (m-1)*floor(card(Molecule n)/m), with natural truncated subtraction. -/
def nearFullPoolSize (n m : ℕ) : ℕ := (m-1)*(Fintype.card (Molecule n)/m)
end HordijkSteelThreshold
end

/- Definition slice: RAFCriticalWindowQuantitative/EscapeEvaluation.lean -/
section
namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open MeasureTheory
/-- Test whether cap-N executable food closure contains a word longer than raw K. -/
def splitEscapeBool (N K : ℕ) (ω : Reaction N → Bool) : Bool :=
  decide (∃ x ∈ computedClosure N 2 (Finset.univ.filter (fun r => ω r)), K < molLength x)
/-- The same raw escape event with canonical quotient marks pulled back to split channels. -/
def quotientEscapeBool (N K : ℕ) (ω : RepositoryChannel N → Bool) : Bool :=
  splitEscapeBool N K (fun r => ω (splitToQuotient r))
/-- Weighted cap-2*(K+2) split escape test with raw threshold K+2, preserving the offset. -/
def splitEscapeEval (q : ℚ) (K : ℕ) : ℚ :=
  rationalEventProbability (Reaction (2*(K+2))) q (splitEscapeBool _ (K+2))
/-- Weighted quotient-coordinate escape test with cap 2*(K+2), raw threshold K+2. -/
def quotientEscapeEval (q : ℚ) (K : ℕ) : ℚ :=
  rationalEventProbability (RepositoryChannel (2*(K+2))) q (quotientEscapeBool _ (K+2))
end RAFCriticalWindowQuantitative
end

/- Definition slice: RAFCriticalWindowQuantitative/FiniteSeedEvaluation.lean -/
section
namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient RAF.Polymer RAF.Concrete
open OverlapCorrectedRAF.Source MeasureTheory
/-- Test acquisition of X_min(N,L) from original food; L>N asks for all ambient molecules. -/
def splitSeedBool (N L : ℕ) (ω : Reaction N → Bool) : Bool :=
  decide (binaryFood N L ⊆ computedClosure N 2 (Finset.univ.filter (fun r => ω r)))
/-- Canonical-quotient version of actual clipped-seed acquisition, with original food. -/
def quotientSeedBool (N L : ℕ) (ω : RepositoryChannel N → Bool) : Bool :=
  splitSeedBool N L (fun r => ω (splitToQuotient r))
/-- Exact rational probability of the split clipped-seed acquisition event. -/
def splitSeedEval (N L : ℕ) (q : ℚ) : ℚ :=
  rationalEventProbability (Reaction N) q (splitSeedBool N L)
/-- Exact rational probability of the quotient clipped-seed acquisition event. -/
def quotientSeedEval (N L : ℕ) (q : ℚ) : ℚ :=
  rationalEventProbability (RepositoryChannel N) q (quotientSeedBool N L)
end RAFCriticalWindowQuantitative
end

/- Definition slice: RAFReactionQuotient/SourceBounds.lean -/
section
namespace RAFReactionQuotient
open Classical Filter MeasureTheory ProbabilityTheory unitInterval HordijkSteelThreshold
open RAF RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
open scoped ENNReal Topology
/-- Existence of an actual nonempty quotient RAF in its own reversible food closure. -/
def quotientRAFEvent (n : ℕ) : Set (RepositoryChannel n → Molecule n → Prop) :=
  {ω | ∃ S, IsRevRAF (repositoryCRS n 2) (fun x j => ω j x) S}
/-- Probability of the literal quotient RAF event under its iid catalytic law. -/
noncomputable def quotientRAFProbability (n : ℕ) (p : I) : ENNReal :=
  quotientCatalyticLaw n p (quotientRAFEvent n)
end RAFReactionQuotient
end

/- Definition slice: RAFCriticalWindowQuantitative/RationalPool.lean -/
section
namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient unitInterval
/-- Exact pool openness 1-(1-p)^k for k independent potential catalysts. -/
def rationalPool (p : ℚ) (k : ℕ) : ℚ := 1-(1-p)^k
end RAFCriticalWindowQuantitative
end

/- Definition slice: RAFCriticalWindowQuantitative/SmallOpenness.lean -/
section
namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAFReactionQuotient RAF.Polymer RAF.Concrete
open OverlapCorrectedRAF.Source MeasureTheory unitInterval
open scoped ENNReal
/-- The literal sparse witness cap 2*(2^(r+1)+2), including r=0. -/
def sparseWitnessCap (r : ℕ) : ℕ := 2*(2^(r+1)+2)
/-- choose(card of split channels at the sparse witness cap,r), not the sharp census. -/
def splitSparseCoefficient (r : ℕ) : ℕ := (Fintype.card (Reaction (sparseWitnessCap r))).choose r
/-- choose(card of quotient channels at the sparse witness cap,r), not the sharp census. -/
def quotientSparseCoefficient (r : ℕ) : ℕ := (Fintype.card (RepositoryChannel (sparseWitnessCap r))).choose r
end RAFCriticalWindowQuantitative
end

/- Definition slice: RAFCriticalWindowQuantitative/GeometricCutoff.lean -/
section
namespace RAFCriticalWindowQuantitative
open Filter
open scoped Topology
/-- Positive-index rational test c*t^r<=eps. -/
def geometricTest (t c ε : ℚ) (r : ℕ) : Prop := 0 < r ∧ c*t^r ≤ ε
/-- The stated decidability/probability instance for the preceding concrete definition. -/
instance (t c ε : ℚ) (r : ℕ) : Decidable (geometricTest t c ε r) :=
  inferInstanceAs (Decidable (_ ∧ _))
/-- Supporting proof obligation; its proof is not imported into this Challenge. -/
theorem geometricTest_exists (t c ε : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hε : 0 < ε) :
    ∃ r, geometricTest t c ε r := by sorry
/-- The least positive geometric-test index; termination is a supporting theorem obligation. -/
def geometricIndex (t c ε : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) (hε : 0 < ε) : ℕ :=
  Nat.find (geometricTest_exists t c ε ht0 ht1 hε)
/-- Supporting proof obligation; its proof is not imported into this Challenge. -/
theorem repair_ratio (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (L : ℕ) :
    0 ≤ 1-q^(L+1) ∧ 1-q^(L+1) < 1 := by sorry
end RAFCriticalWindowQuantitative
end

/- Definition slice: RAFCriticalWindowQuantitative/ApproximationParameters.lean -/
section
namespace RAFCriticalWindowQuantitative
theorem rationalHalf_pos (q : ℚ) (hq : 0 < q) : 0 < q/2 :=
  div_pos hq zero_lt_two

theorem rationalHalf_le_one (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) : q/2 ≤ 1 :=
  (div_le_self hq.le one_le_two).trans hq1

/-- Natural ceiling of 4/eps, plus 2; used on positive valid tolerances. -/
def precisionIndex (ε : ℚ) : ℕ := ⌈4/ε⌉₊+2
/-- Least positive r with 2^(L+1)*(1-q^(L+1))^r<=eps/4; actual q in both models. -/
def recordIndex (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (L : ℕ)
    (ε : ℚ) (hε : 0 < ε) : ℕ :=
  geometricIndex (1-q^(L+1)) (2^(L+1)) (ε/4)
    (repair_ratio q hq hq1 L).1 (repair_ratio q hq hq1 L).2 (by positivity)
end RAFCriticalWindowQuantitative
end

/- Definition slice: RAFCriticalWindowQuantitative/CertifiedEvaluator.lean -/
section
namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient MeasureTheory
/-- Computed raw cap from seed openness q and the positive-tolerance geometric selector. -/
def splitEvaluationCap (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℕ :=
  let L := 10*seedIndex q hq hq1 (precisionIndex ε)
  recordCap L (recordIndex q hq hq1 L ε hε)
/-- The raw rational pair (escape-eps/2,escape) at the computed split raw cap. -/
def splitCertifiedInterval (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℚ × ℚ :=
  let e := splitEscapeEval q (splitEvaluationCap q hq hq1 ε hε-2)
  (e-ε/2,e)
end RAFCriticalWindowQuantitative
end

/- Definition slice: RAFCriticalWindowQuantitative/QuotientCertifiedEvaluator.lean -/
section
namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient MeasureTheory
/-- Computed raw cap using q/2 for the seed selector and q for the repair selector. -/
def quotientEvaluationCap (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℕ :=
  let hhalf : 0 < q/2 := rationalHalf_pos q hq
  let hhalf1 : q/2 ≤ 1 := rationalHalf_le_one q hq hq1
  let L := 10*seedIndex (q/2) hhalf hhalf1 (precisionIndex ε)
  recordCap L (recordIndex q hq hq1 L ε hε)
/-- The raw rational pair (escape-eps/2,escape) at the computed quotient raw cap. -/
def quotientCertifiedInterval (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℚ × ℚ :=
  let e := quotientEscapeEval q (quotientEvaluationCap q hq hq1 ε hε-2)
  (e-ε/2,e)
end RAFCriticalWindowQuantitative
end

/- Definition slice: RAFCriticalWindowQuantitative/Endpoints.lean -/
section
namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient unitInterval
/-- Total valid-input split evaluator: (0,0) at q=0; certified raw interval otherwise. -/
def splitTotalInterval (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℚ × ℚ :=
  if h : q = 0 then (0,0) else splitCertifiedInterval q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε
/-- Total valid-input quotient evaluator: (0,0) at q=0; certified raw interval otherwise. -/
def quotientTotalInterval (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) : ℚ × ℚ :=
  if h : q = 0 then (0,0) else quotientCertifiedInterval q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε
end RAFCriticalWindowQuantitative
end

/- Definition slice: RAFCriticalWindowQuantitative/SourceContract.lean -/
section
namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval RAF.Polymer RAF.Concrete
open scoped ENNReal
/-- The source clamped split RAF law at intensity p*card(Reaction n)/n. -/
noncomputable def splitCatalyticProbability (n : ℕ) (p : I) : ENNReal :=
  uniformCatalysisMeasure n ((p : ℝ)*Fintype.card (Reaction n)/n) (HasRAFEvent n)
/-- Actual seed lower endpoint and finite escape upper endpoint with gateway constant 36. -/
def splitSourceInterval (n m K : ℕ) (p q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) : ℚ × ℚ :=
  (splitSeedEval n (10*seedIndex q hq hq1 m) q - 1/m,
    splitEscapeEval (rationalPool p (Fintype.card (Molecule n))) K +
      (Fintype.card (Molecule (K+2)) : ℚ)*36*p)
/-- Quotient seed lower endpoint and finite escape upper endpoint with gateway constant 34. -/
def quotientSourceInterval (n m K : ℕ) (p q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) : ℚ × ℚ :=
  let hh : 0 < q/2 := rationalHalf_pos q hq
  let hh1 : q/2 ≤ 1 := rationalHalf_le_one q hq hq1
  (quotientSeedEval n (10*seedIndex (q/2) hh hh1 m) q - 1/m,
    quotientEscapeEval (rationalPool p (Fintype.card (Molecule n))) K +
      (Fintype.card (Molecule (K+2)) : ℚ)*34*p)
end RAFCriticalWindowQuantitative
end

/- Definition slice: RAFCriticalWindowQuantitative/SourceCalibration.lean -/
section
namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient MeasureTheory unitInterval RAF.Polymer RAF.Concrete
open Filter
open scoped Topology
/-- Interval comparison certificate max(uP-lS,uS-lP), preserving raw endpoints. -/
def rationalIntervalError (source profile : ℚ × ℚ) : ℚ :=
  max (source.2-profile.1) (profile.2-source.1)
end RAFCriticalWindowQuantitative
end

/- Definition slice: RAFReactionQuotient/Resolution.lean -/
section
namespace RAFReactionQuotient
open Classical Filter MeasureTheory unitInterval HordijkSteelThreshold RAF.Polymer
open OverlapCorrectedRAF.Source OverlapCorrectedRAF.Asymptotic
open scoped ENNReal Topology
/-- The actual critical openness 1-exp(-lambda), for positive real intensity lambda. -/
noncomputable def criticalOpenness (lambda : ℝ) (hlambda : 0 < lambda) : I :=
  ⟨1-Real.exp (-lambda), by
    constructor
    · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
    · linarith [Real.exp_pos (-lambda)]⟩
end RAFReactionQuotient
end

/- Definition slice: RAFCriticalWindowQuantitative/ProductiveHistory.lean -/
section
namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAF.Concrete RAF.Polymer RAFReactionQuotient OverlapCorrectedRAF.Source
/-- Reversible closure after card(M) rounds; stabilization/least-closure agreement is an obligation. -/
def fullClosure {M R : Type*} [Fintype M] [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) : Finset M := revClosureAt Q S (Fintype.card M)
/-- Inductively choose distinct channels of S that strictly enlarge closure under prior choices. -/
inductive ProductiveHistory {M R : Type*} [Fintype M] [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) : ℕ → Finset R → Prop
  | nil : ProductiveHistory Q S 0 ∅
  | step {k T r} : ProductiveHistory Q S k T → r ∈ S → r ∉ T →
      revClosureStep Q {r} (fullClosure Q T) ≠ fullClosure Q T →
      ProductiveHistory Q S (k+1) (insert r T)
end RAFCriticalWindowQuantitative
end

/- Definition slice: RAFCriticalWindowQuantitative/Resolution.lean -/
section
namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient unitInterval RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source
/-- The four exact profile conclusions, instantiated below with concrete laws and algorithms. -/
structure ProfileGuarantees (S : I → ENNReal) (escape : I → ℕ → ENNReal)
    (evaluate : (q : ℚ) → 0 ≤ q → q ≤ 1 → (ε : ℚ) → 0 < ε → ℚ × ℚ)
    (cap : (q : ℚ) → 0 < q → q ≤ 1 → (ε : ℚ) → 0 < ε → ℕ)
    (coefficient : ℕ → ℕ) : Prop where
  enclosure : ∀ q hq hq1 ε hε,
    let v := evaluate q hq hq1 ε hε
    (v.1 : ℝ) ≤ (S (rationalParameter q hq hq1)).toReal ∧
      (S (rationalParameter q hq hq1)).toReal ≤ (v.2 : ℝ) ∧ v.2-v.1 < ε
  uniform_error : ∀ q hq hq1 ε hε a, rationalParameter q (le_of_lt hq) hq1 ≤ a →
    (escape a (cap q hq hq1 ε hε)).toReal ≤ (S a).toReal+(ε : ℝ)/2
  power_bound : ∀ a r, (S a).toReal ≤ (coefficient r : ℝ)*(a : ℝ)^r
  intensity_flatness : ∀ d ε, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ lam : ℝ, ∀ hlam : 0 < lam, lam < δ → (S (criticalOpenness lam hlam)).toReal < ε*lam^d
/-- Exact split/quotient input-dependent comparison; retain all independent inputs and pool hypotheses. -/
def SourceGuarantees : Prop :=
  (∀ n m K, ∀ _hn : 4 ≤ n, ∀ _hm : 0 < m,
    ∀ p hp hp1 q hq hq1, ∀ _hk : 6 < nearFullPoolSize n m,
    ∀ _hpool : q ≤ rationalPool p (nearFullPoolSize n m),
    ∀ s hs hs1 ε hε,
    |(splitCatalyticProbability n (rationalParameter p hp hp1)).toReal -
      (staticSurvival (rationalParameter s hs hs1)).toReal| ≤
      (rationalIntervalError (splitSourceInterval n m K p q hq hq1)
        (splitTotalInterval s hs hs1 ε hε) : ℝ)) ∧
  (∀ n m K, ∀ _hn : 0 < n, ∀ _hm : 0 < m,
    ∀ p hp hp1 q hq hq1, ∀ _hk : 6 < nearFullPoolSize n m,
    ∀ _hpool : q ≤ rationalPool p (nearFullPoolSize n m),
    ∀ s hs hs1 ε hε,
    |(quotientRAFProbability n (rationalParameter p hp hp1)).toReal -
      (quotientSurvival (rationalParameter s hs hs1)).toReal| ≤
      (rationalIntervalError (quotientSourceInterval n m K p q hq hq1)
        (quotientTotalInterval s hs hs1 ε hε) : ℝ))
/-- Selected complete quantitative assertion for both literal models. -/
theorem quantitative_critical_window_resolution :
    ProfileGuarantees staticSurvival splitEscapeProbability
      splitTotalInterval splitEvaluationCap splitSparseCoefficient ∧
    ProfileGuarantees quotientSurvival quotientEscapeProbability
      quotientTotalInterval quotientEvaluationCap quotientSparseCoefficient ∧
    SourceGuarantees ∧
    (∀ N k S x, x ∈ temporaryReactionClosure (N := N) 2 S → 2^(k+1) < molLength x →
      ∃ T, ProductiveHistory (binaryPolymerCRS N 2) S k T ∧ T.card = k ∧ T ⊆ S) ∧
    (∀ N k S x, x ∈ quotientClosure N 2 S → 2^(k+1) < molLength x →
      ∃ T, ProductiveHistory (repositoryCRS N 2) S k T ∧ T.card = k ∧ T ⊆ S) ∧
    (∀ a : I, (a : ℝ) ≤ 1/10^20 → (staticSurvival a).toReal < 8/10^26) := by sorry
end RAFCriticalWindowQuantitative
end
