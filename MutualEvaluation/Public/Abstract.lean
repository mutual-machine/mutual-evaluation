import MutualEvaluation.Internal.AbstractProofs
noncomputable section

namespace MutualEvaluation.Abstract

/- AUTHOR-SPAN AB-01
When the evaluation or return types $X$ or $R$ appear in this section they refer
to the mutual evaluation game $G$. We refer to $(X,R)$ as the evaluation task type. -/
variable {X R : Type} (G : Game X R)

/-- AUTHOR-SPAN AB-02
We define critic regret as the difference between the supremal game valuation
and critic evaluation score. -/
def regret (c : R × R → G.S) (ρ : PMF (TwoPairOutcome R)) : ℝ :=
  V G ρ - G.u c ρ

/- AUTHOR-SPAN AB-03
The evaluation score is equal to the game valuation minus critic regret.
This regret is nonnegative and equal to zero if and only if the critic evaluation
score is the supremal game valuation. -/
theorem payoff_eq_value_sub_regret (c : R × R → G.S) (ρ : PMF (TwoPairOutcome R)) :
    G.u c ρ = V G ρ - regret G c ρ :=
  Internal.AbstractProofs.payoff_eq_value_sub_regret G c ρ

theorem regret_nonneg [Fintype R] (c : R × R → G.S) (ρ : PMF (TwoPairOutcome R)) :
    0 ≤ regret G c ρ :=
  Internal.AbstractProofs.regret_nonneg G c ρ

theorem regret_zero_iff (c : R × R → G.S) (ρ : PMF (TwoPairOutcome R)) :
    regret G c ρ = 0 ↔ G.u c ρ = V G ρ :=
  Internal.AbstractProofs.regret_zero_iff G c ρ

/-- AUTHOR-SPAN AB-04
One corollary is that every outcome law has a critic rule that achieves zero regret. -/
theorem regret_attained [Fintype R] (ρ : PMF (TwoPairOutcome R)) :
    ∃ c : R × R → G.S, regret G c ρ = 0 :=
  Internal.AbstractProofs.regret_attained G ρ

/- AUTHOR-SPAN AB-05
These results depend on the finite, nonempty critic rule set, not the game's
robustness property. The supremum exists because of finite maximum attainment.
There is also a converse. -/
def withRegret (F : PMF (TwoPairOutcome R) → ℝ)
    (r : (R × R → G.S) → PMF (TwoPairOutcome R) → ℝ) : Game X R :=
  { G with u := fun c ρ => F ρ - r c ρ }

/-- AUTHOR-SPAN AB-06
Pointwise normalization realizes both the chosen value and the chosen regret.
The zero-regret critic may depend on the law. -/
theorem realizes_regret [Fintype R]
    (F : PMF (TwoPairOutcome R) → ℝ)
    (r : (R × R → G.S) → PMF (TwoPairOutcome R) → ℝ)
    (hn : ∀ c ρ, 0 ≤ r c ρ) (hz : ∀ ρ, ∃ c, r c ρ = 0)
    (ρ : PMF (TwoPairOutcome R)) :
    V (withRegret G F r) ρ = F ρ ∧
      ∀ c, regret (withRegret G F r) c ρ = r c ρ :=
  Internal.AbstractProofs.realizes_regret G F r hn hz ρ

/- AUTHOR-SPAN AB-07
Another result that generates a corollary is that evaluation scores with the same
outcome law, worker channels, and envelope - i.e. identical supremal valuations -
also have the same robustness condition. -/

theorem same_value_robustness_iff (H : Game X R)
    (hP : G.P = H.P) (hw : G.w = H.w)
    (hV : ∀ ρ, V G ρ = V H ρ) :
    robust G ↔ robust H :=
  Internal.AbstractProofs.same_value_robustness_iff G H hP hw hV

/- AUTHOR-SPAN AB-08
The robustness condition constrains the envelope along the admisible worker
garblings of the generated laws. However, the critic regret is not determined by
this property. There is further structure, however. If evaluation score gaps do
not depend on the choice of critic then critic regret is law-independent and
evaluation scores are separable. -/

/-! All-law statements: rho and nu need not be reachable reporting laws. -/

theorem gap_iff_regret_invariant [Fintype R] :
    (∀ c d ρ ν, G.u c ρ - G.u c ν = G.u d ρ - G.u d ν) ↔
      ∀ c ρ ν, regret G c ρ = regret G c ν :=
  Internal.AbstractProofs.gap_iff_regret_invariant_on G id

theorem gap_iff_separable :
    (∀ c d ρ ν, G.u c ρ - G.u c ν = G.u d ρ - G.u d ν) ↔
      ∃ (F : PMF (TwoPairOutcome R) → ℝ) (B : (R × R → G.S) → ℝ),
        ∀ c ρ, G.u c ρ = F ρ + B c :=
  Internal.AbstractProofs.gap_iff_separable_on G id (law G truth)

/-! Reachable-law statements: quantify over all local reporting profiles.
No off-image condition is imposed on the payoff or regret. -/

theorem reporting_gap_iff_regret_invariant [Fintype R] :
    (∀ c d σ τ, G.u c (law G σ) - G.u c (law G τ) =
      G.u d (law G σ) - G.u d (law G τ)) ↔
      ∀ c σ τ, regret G c (law G σ) = regret G c (law G τ) :=
  Internal.AbstractProofs.gap_iff_regret_invariant_on G (law G)

theorem reporting_gap_iff_separable :
    (∀ c d σ τ, G.u c (law G σ) - G.u c (law G τ) =
      G.u d (law G σ) - G.u d (law G τ)) ↔
      ∃ (F : (Fin 2 → Kernel R R) → ℝ) (B : (R × R → G.S) → ℝ),
        ∀ c σ, G.u c (law G σ) = F σ + B c :=
  Internal.AbstractProofs.gap_iff_separable_on G (law G) truth

/- AUTHOR-SPAN AB-11
This result quantifies over all available outcome laws and does not impose any condition
outside the admissible set. Generally, there will not be equality between different
critic regret. The global validity condition introduced later is about a different
question: whether the critic's comparisons define an equivalence relation on the
entire completion return alphabet. The following identity is useful to understand
the conditional situation. -/

theorem committed_loss (c : R × R → G.S) (ρ ν : PMF (TwoPairOutcome R))
    (hc : G.u c ρ = V G ρ) :
    G.u c ρ - G.u c ν = (V G ρ - V G ν) + regret G c ν :=
  Internal.AbstractProofs.committed_loss G c ρ ν hc

/- AUTHOR-SPAN AB-12
So if $\rho$ is generated and $\nu$ comes from admissible worker garbling, the
robustness property guarnatees the value loss is nonnegative, or strictly positive
when the cross marginal of $\rho$ is dependent and that of $\nu$ is not. This shows
a value-preserving garbling can lower the committed payoff through the new-law
regret. Reoptimizing the critic removes the regret term while holding the critic
fixed need not. -/

end MutualEvaluation.Abstract

end