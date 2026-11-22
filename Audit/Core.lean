import MutualEvaluation.Public.Core

/-! Technical inspection of the annotated Core. This file is not an annotation. -/
open MutualEvaluation

#print Kernel
#print pair
#print Score
#print Score.envelope
#print independent
#print Binary.scores
#print Binary.Critic
#print Probability.mass
#print jointLaw
#print Kernel.replicate
#print Kernel.truth
#print truth
#print deviate
#print Kernel.garble
#print garble
#print robustUnderGarbling

#print axioms Kernel
#print axioms pair
#print axioms Score
#print axioms Score.envelope
#print axioms independent
#print axioms Binary.scores
#print axioms Binary.Critic
#print axioms Probability.mass
#print axioms jointLaw
#print axioms Kernel.replicate
#print axioms Kernel.truth
#print axioms truth
#print axioms deviate
#print axioms Kernel.garble
#print axioms garble
#print axioms robustUnderGarbling

/-! Shared-only clients need no assumptions on the outcome type. -/
noncomputable section
variable {R Outcome : Type}

example (U : Score R (PMF Outcome)) (ρ : PMF Outcome) : ℝ :=
  U.envelope ρ

example (U : Score R (PMF (List R))) (ρ : PMF (List R)) : ℝ :=
  U.envelope ρ

example : Score R (PMF (List R)) :=
  ⟨{0}, by simp, fun _ _ => 0⟩

example : Kernel R R := PMF.pure

example : Binary.Critic R :=
  fun _ => ⟨0, by simp [Binary.scores]⟩

example (ρ : PMF Outcome) (a : Outcome) : ℝ :=
  Probability.mass ρ a

end