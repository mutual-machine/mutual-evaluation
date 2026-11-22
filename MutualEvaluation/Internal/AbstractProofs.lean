import MutualEvaluation.Public.TwoPairOutcome

/-!
INTERNAL — proof support for the author's annotated Abstract interface.
The conclusions use TwoPairOutcome expressions directly; this module does not define
the public regret or payoff-replacement constructions.
No declaration here is an additional author-certified paper statement.
-/

noncomputable section
namespace MutualEvaluation.Internal.AbstractProofs
variable {X R : Type} (G : Game X R)

private theorem policy_nonempty : Nonempty (R × R → G.S) := by
  obtain ⟨s, hs⟩ := G.nonempty
  exact ⟨fun _ => ⟨s, hs⟩⟩

private theorem le_value [Fintype R] (ρ : PMF (TwoPairOutcome R))
    (c : R × R → G.S) : G.u c ρ ≤ V G ρ := by
  classical
  have hf : (Set.range fun d => G.u d ρ).Finite := Set.finite_range _
  exact le_csSup hf.bddAbove ⟨c, rfl⟩

private theorem exists_eq_value [Fintype R] (ρ : PMF (TwoPairOutcome R)) :
    ∃ c : R × R → G.S, G.u c ρ = V G ρ := by
  classical
  have hf : (Set.range fun c => G.u c ρ).Finite := Set.finite_range _
  obtain ⟨c⟩ := policy_nonempty G
  have hne : (Set.range fun d => G.u d ρ).Nonempty := ⟨G.u c ρ, ⟨c, rfl⟩⟩
  exact hne.csSup_mem hf

theorem payoff_eq_value_sub_regret (c : R × R → G.S) (ρ : PMF (TwoPairOutcome R)) :
    G.u c ρ = V G ρ - (V G ρ - G.u c ρ) := by
  ring

theorem regret_nonneg [Fintype R] (c : R × R → G.S) (ρ : PMF (TwoPairOutcome R)) :
    0 ≤ V G ρ - G.u c ρ :=
  sub_nonneg.mpr (le_value G ρ c)

theorem regret_zero_iff (c : R × R → G.S) (ρ : PMF (TwoPairOutcome R)) :
    V G ρ - G.u c ρ = 0 ↔ G.u c ρ = V G ρ :=
  sub_eq_zero.trans eq_comm

theorem regret_attained [Fintype R] (ρ : PMF (TwoPairOutcome R)) :
    ∃ c : R × R → G.S, V G ρ - G.u c ρ = 0 := by
  obtain ⟨c, hc⟩ := exists_eq_value G ρ
  exact ⟨c, sub_eq_zero.mpr hc.symm⟩

theorem realizes_regret [Fintype R]
    (F : PMF (TwoPairOutcome R) → ℝ)
    (r : (R × R → G.S) → PMF (TwoPairOutcome R) → ℝ)
    (hn : ∀ c ρ, 0 ≤ r c ρ) (hz : ∀ ρ, ∃ c, r c ρ = 0)
    (ρ : PMF (TwoPairOutcome R)) :
    V ({ G with u := fun c ν => F ν - r c ν } : Game X R) ρ = F ρ ∧
      ∀ c, V ({ G with u := fun d ν => F ν - r d ν } : Game X R) ρ -
        (F ρ - r c ρ) = r c ρ := by
  let H : Game X R := { G with u := fun c ν => F ν - r c ν }
  change V H ρ = F ρ ∧ ∀ c, V H ρ - (F ρ - r c ρ) = r c ρ
  have hv : V H ρ = F ρ := by
    apply le_antisymm
    · obtain ⟨c, hc⟩ := exists_eq_value H ρ
      rw [← hc]
      exact sub_le_self _ (hn c ρ)
    · obtain ⟨c, hc⟩ := hz ρ
      calc
        F ρ = H.u c ρ := by
          change F ρ = F ρ - r c ρ
          rw [hc, sub_zero]
        _ ≤ V H ρ := le_value H ρ c
  refine ⟨hv, ?_⟩
  intro c
  rw [hv]
  ring

theorem same_value_robustness_iff (H : Game X R)
    (hP : G.P = H.P) (hw : G.w = H.w)
    (hV : ∀ ρ, V G ρ = V H ρ) :
    robust G ↔ robust H := by
  have hl : law G = law H := by
    funext σ
    simp only [law, hP, hw]
  simp only [robust, robustAt, robustUnderGarbling, Function.comp_apply, hl, hV]

theorem gap_iff_regret_invariant_on [Fintype R] {L : Type}
    (g : L → PMF (TwoPairOutcome R)) :
    (∀ c d l k, G.u c (g l) - G.u c (g k) =
      G.u d (g l) - G.u d (g k)) ↔
      ∀ c l k, V G (g l) - G.u c (g l) = V G (g k) - G.u c (g k) := by
  constructor
  · intro h c l k
    obtain ⟨d, hd⟩ := exists_eq_value G (g l)
    obtain ⟨e, he⟩ := exists_eq_value G (g k)
    have hde := h d e l k
    have hcd := h c d l k
    have hdk := le_value G (g k) d
    have hel := le_value G (g l) e
    linarith
  · intro h c d l k
    have hc := h c l k
    have hd := h d l k
    linarith

theorem gap_iff_separable_on {L : Type}
    (g : L → PMF (TwoPairOutcome R)) (l₀ : L) :
    (∀ c d l k, G.u c (g l) - G.u c (g k) =
      G.u d (g l) - G.u d (g k)) ↔
      ∃ (F : L → ℝ) (B : (R × R → G.S) → ℝ),
        ∀ c l, G.u c (g l) = F l + B c := by
  constructor
  · intro h
    obtain ⟨c₀⟩ := policy_nonempty G
    refine ⟨fun l => G.u c₀ (g l),
      fun c => G.u c (g l₀) - G.u c₀ (g l₀), ?_⟩
    intro c l
    have he := h c c₀ l l₀
    dsimp
    linarith
  · rintro ⟨F, B, h⟩ c d l k
    rw [h, h, h, h]
    ring

theorem committed_loss (c : R × R → G.S) (ρ ν : PMF (TwoPairOutcome R))
    (hc : G.u c ρ = V G ρ) :
    G.u c ρ - G.u c ν = (V G ρ - V G ν) + (V G ν - G.u c ν) := by
  rw [hc]
  ring

end MutualEvaluation.Internal.AbstractProofs
end