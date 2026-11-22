import MutualEvaluation.Public.CriticTiming

/-! INTERNAL — implementation and proof support; not an author-certified annotation file. -/

/-!
#  paper results — transfer and equilibrium

Two review sections: envelope/commitment and reporting/equilibrium.
All results are derived, not additional Game fields. Equality to V states
critic optimality; finite R is explicit wherever the upper bound is used.
Reporter indices are 0 and 1. Robustness concerns only index 0.
-/

noncomputable section
namespace MutualEvaluation.Abstract
variable {X R : Type} (G : Game X R)

/-! ## Payoff transfer -/

/-- The new-law critic d need not be the committed old-law critic c. -/
theorem transfer_le [Fintype R] (c d : R × R → G.S) (ρ ν : PMF (TwoPairOutcome R))
    (hc : G.u c ρ = V G ρ) (hv : V G ν ≤ V G ρ) :
    G.u d ν ≤ G.u c ρ := by
  rw [hc]
  exact (sub_nonneg.mp (regret_nonneg G d ν)).trans hv

theorem transfer_lt [Fintype R] (c d : R × R → G.S) (ρ ν : PMF (TwoPairOutcome R))
    (hc : G.u c ρ = V G ρ) (hv : V G ν < V G ρ) :
    G.u d ν < G.u c ρ := by
  rw [hc]
  exact lt_of_le_of_lt (sub_nonneg.mp (regret_nonneg G d ν)) hv

/-- Weak loss, and strict loss under the original cross-independence trigger.
The same atomic kernel is applied independently on both first-worker replicas. -/
theorem garbling_loss [Fintype R] (h : robust G)
    (σ : Fin 2 → Kernel R R) (τ : Kernel R R) (c d : R × R → G.S)
    (hc : G.u c (law G σ) = V G (law G σ)) :
    let ν := law G (Function.update σ 0 (fun a => (σ 0 a).bind τ))
    G.u d ν ≤ G.u c (law G σ) ∧
      (¬ independent (cross (law G σ)) → independent (cross ν) →
        G.u d ν < G.u c (law G σ)) := by
  exact ⟨transfer_le G c d _ _ hc (h σ τ).1,
    fun hd hi => transfer_lt G c d _ _ hc ((h σ τ).2 hd hi)⟩

/-! ## B2. Value maximality and truthful equilibrium -/

/-- One-sided robustness supports truth against this fixed peer only when
the critic is optimal at that truthful-first-worker law. -/
theorem first_reporter_best_response [Fintype R] (h : robust G)
    (σ : Fin 2 → Kernel R R) (c : R × R → G.S)
    (hc : G.u c (law G (Function.update σ 0 PMF.pure)) =
      V G (law G (Function.update σ 0 PMF.pure))) (τ : Kernel R R) :
    G.u c (law G (Function.update σ 0 τ)) ≤
      G.u c (law G (Function.update σ 0 PMF.pure)) := by
  apply transfer_le G c c _ _ hc
  have hτ : Kernel.garble (PMF.pure : Kernel R R) τ = τ := by
    funext a
    exact PMF.pure_bind a τ
  simpa [garble, deviate, hτ] using (h (Function.update σ 0 PMF.pure) τ).1

/-- The displayed second-worker bound is additional; it does not follow
from robustness. No finite type hypothesis is needed for this value comparison. -/
theorem truth_value_maximal_of_robustness (h : robust G)
    (h₂ : ∀ τ, V G (law G (Function.update truth 1 τ)) ≤ V G (law G truth)) :
    truthValueMaximal G := by
  intro σ
  let s : Fin 2 → Kernel R R := Function.update truth 1 (σ 1)
  have hs : Function.update s 0 (fun a => (s 0 a).bind (σ 0)) = σ := by
    funext i
    fin_cases i <;> simp [s, truth, PMF.pure_bind]
  have hv : V G (law G (Function.update s 0 (fun a => (s 0 a).bind (σ 0)))) ≤ V G (law G s) :=
    (h s (σ 0)).1
  rw [hs] at hv
  exact hv.trans (h₂ (σ 1))

theorem truthful_nash_of_value_maximal [Fintype R] (h : truthValueMaximal G)
    (c : R × R → G.S) (hc : G.u c (law G truth) = V G (law G truth)) :
    nash G truth c := by
  exact ⟨fun d => truthful_global_optimal G h c hc d truth,
    fun i τ => truthful_global_optimal G h c hc c (Function.update truth i τ)⟩

/-- Direct value maximality suffices, including for peer-free constructions
which have not been packaged as robust Models. -/
theorem exists_truthful_nash [Fintype R] (h : truthValueMaximal G) :
    ∃ c, nash G truth c := by
  obtain ⟨c, hc⟩ := regret_attained G (law G truth)
  exact ⟨c, truthful_nash_of_value_maximal G h c
    ((regret_zero_iff G c (law G truth)).1 hc)⟩

end MutualEvaluation.Abstract
end