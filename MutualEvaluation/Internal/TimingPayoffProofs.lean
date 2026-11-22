import MutualEvaluation.Public.Abstract
import MutualEvaluation.Internal.BooleanDependence

/-! INTERNAL — implementation and proof support; not an author-certified annotation file. -/

/-!
# Boolean timing comparison — expected-payoff functionals

The joint-minus-product objective has exactly the total-variation envelope
over all binary critics. Two games share that envelope but not regret.
This is the finite Boolean objective correspondence, not a general CA/VPP
learning or informed-truthfulness theorem. Sampling implementations are separate.
-/

noncomputable section
namespace MutualEvaluation.Timing
open Boolean Probability Probability.Proofs Abstract

local notation "mass" => (fun {A : Type} (p : PMF A) (a : A) => ENNReal.toReal (p a))
local notation "scores" => ({0, 1} : Finset ℝ)
local notation "Critic" => (fun R : Type => R × R → ({0, 1} : Finset ℝ))

/-- Joint expectation minus expectation under independent marginal draws. -/
def J (c : Critic Bool) (μ : PMF (Bool × Bool)) : ℝ :=
  (∑ p, mass μ p * (c p : ℝ)) -
    ∑ p, (mass (μ.map Prod.fst) p.1 * mass (μ.map Prod.snd) p.2) * (c p : ℝ)

def agree : Critic Bool := fun p =>
  if p.1 = p.2 then ⟨1, by simp⟩ else ⟨0, by simp⟩
def disagree : Critic Bool := fun p =>
  if p.1 = p.2 then ⟨0, by simp⟩ else ⟨1, by simp⟩

private theorem score_bounds (c : Critic Bool) (p : Bool × Bool) :
    0 ≤ (c p : ℝ) ∧ (c p : ℝ) ≤ 1 := by
  have h : (c p : ℝ) = 0 ∨ (c p : ℝ) = 1 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using (c p).property
  rcases h with h | h <;> simp [h]

private def contrast (c : Critic Bool) : ℝ :=
  (c (false, false) : ℝ) + (c (true, true) : ℝ) -
    (c (false, true) : ℝ) - (c (true, false) : ℝ)

private theorem contrast_bounds (c : Critic Bool) :
    -2 ≤ contrast c ∧ contrast c ≤ 2 := by
  have h₀ := score_bounds c (false, false)
  have h₁ := score_bounds c (false, true)
  have h₂ := score_bounds c (true, false)
  have h₃ := score_bounds c (true, true)
  unfold contrast
  constructor <;> linarith

private theorem contrast_agree : contrast agree = 2 := by
  norm_num [contrast, agree]

private theorem contrast_disagree : contrast disagree = -2 := by
  norm_num [contrast, disagree]

private theorem J_formula (c : Critic Bool) (μ : PMF (Bool × Bool)) :
    J c μ = determinant μ * contrast c := by
  unfold J
  rw [← Finset.sum_sub_distrib]
  simp only [← sub_mul, Fintype.sum_prod_type, Boolean.residual]
  simp [contrast]
  ring

private theorem J_le_TV (c : Critic Bool) (μ : PMF (Bool × Bool)) :
    J c μ ≤ TV μ := by
  rw [J_formula, TV_eq]
  have hb := contrast_bounds c
  by_cases h : 0 ≤ determinant μ
  · rw [D, abs_of_nonneg h]
    nlinarith [hb.2]
  · have hn : determinant μ ≤ 0 := le_of_lt (lt_of_not_ge h)
    rw [D, abs_of_nonpos hn]
    nlinarith [hb.1]

/-- Exact binary variational formula; no unrestricted score space is needed. -/
theorem variational_TV (μ : PMF (Bool × Bool)) :
    (∀ c : Critic Bool, J c μ ≤ TV μ) ∧ ∃ c : Critic Bool, J c μ = TV μ := by
  refine ⟨fun c => J_le_TV c μ, ?_⟩
  by_cases h : 0 ≤ determinant μ
  · refine ⟨agree, ?_⟩
    rw [J_formula, contrast_agree, TV_eq, D, abs_of_nonneg h]
    ring
  · refine ⟨disagree, ?_⟩
    rw [J_formula, contrast_disagree, TV_eq, D,
      abs_of_nonpos (le_of_lt (lt_of_not_ge h))]
    ring

variable {X : Type} (P : PMF X) (f : Fin 2 → Kernel X Bool)

def bonusGame : Game X Bool where
  P := P
  w := f
  S := scores
  nonempty := by simp
  u := fun c ρ => TV (cross ρ) / 2 + (c (false, false) : ℝ)

def mediatedGame : Game X Bool :=
  { bonusGame P f with u := fun c ρ => 1 + J c (cross ρ) / 2 }

/-! Proof helpers use maximum attainment, not legacy certificates. -/
private theorem value_of_max (G : Game X Bool) (ρ : PMF (TwoPairOutcome Bool)) (F : ℝ)
    (hu : ∀ c, G.u c ρ ≤ F) (ha : ∃ c, G.u c ρ = F) : V G ρ = F := by
  obtain ⟨c, hc⟩ := regret_attained G ρ
  have hc' := (regret_zero_iff G c ρ).1 hc
  obtain ⟨d, hd⟩ := ha
  exact le_antisymm (hc' ▸ hu c)
    (hd ▸ sub_nonneg.mp (regret_nonneg G d ρ))

theorem values (ρ : PMF (TwoPairOutcome Bool)) :
    V (bonusGame P f) ρ = 1 + TV (cross ρ) / 2 ∧
      V (mediatedGame P f) ρ = 1 + TV (cross ρ) / 2 := by
  constructor
  · apply value_of_max
    · intro c
      change TV (cross ρ) / 2 + (c (false, false) : ℝ) ≤ 1 + TV (cross ρ) / 2
      linarith [(score_bounds c (false, false)).2]
    · refine ⟨agree, ?_⟩
      change TV (cross ρ) / 2 + (agree (false, false) : ℝ) = 1 + TV (cross ρ) / 2
      norm_num [agree]
      ring
  · apply value_of_max
    · intro c
      change 1 + J c (cross ρ) / 2 ≤ 1 + TV (cross ρ) / 2
      linarith [(variational_TV (cross ρ)).1 c]
    · obtain ⟨c, hc⟩ := (variational_TV (cross ρ)).2
      refine ⟨c, ?_⟩
      change 1 + J c (cross ρ) / 2 = 1 + TV (cross ρ) / 2
      rw [hc]

theorem regrets (c : Critic Bool) (ρ : PMF (TwoPairOutcome Bool)) :
    regret (bonusGame P f) c ρ = 1 - (c (false, false) : ℝ) ∧
      regret (mediatedGame P f) c ρ = (TV (cross ρ) - J c (cross ρ)) / 2 := by
  unfold regret
  rw [(values P f ρ).1, (values P f ρ).2]
  change
    1 + TV (cross ρ) / 2 - (TV (cross ρ) / 2 + (c (false, false) : ℝ)) = _ ∧
      1 + TV (cross ρ) / 2 - (1 + J c (cross ρ) / 2) = _
  constructor <;> ring

private theorem robust_of_envelope (G : Game X Bool)
    (hv : ∀ ρ, V G ρ = 1 + TV (cross ρ) / 2) : robust G := by
  intro σ τ
  have hgarble : garble σ 0 τ = Function.update σ 0 (fun a => (σ 0 a).bind τ) := rfl
  simp only [robustUnderGarbling, Function.comp_apply, hgarble]
  have hs : (fun i a => (σ i a).bind (Function.update truth 0 τ i)) =
      Function.update σ 0 (fun a => (σ 0 a).bind τ) := by
    funext i a
    fin_cases i <;> simp [truth, PMF.bind_pure]
  have hl := cross_law_post G σ (Function.update truth 0 τ)
  rw [hs] at hl
  have hb : D (cross (law G (Function.update σ 0 (fun a => (σ 0 a).bind τ)))) ≤
      D (cross (law G σ)) := by
    rw [hl]
    exact data_processing _ _ _
  constructor
  · simp only [hv, TV_eq]
    linarith
  · intro hd hi
    have hp := (D_pos_iff _).2 hd
    have hz := (D_zero_iff _).2 hi
    simp only [hv, TV_eq]
    linarith

theorem robust_games : robust (bonusGame P f) ∧ robust (mediatedGame P f) :=
  ⟨robust_of_envelope _ (fun ρ => (values P f ρ).1),
    robust_of_envelope _ (fun ρ => (values P f ρ).2)⟩

private theorem maximal_of_envelope (G : Game X Bool)
    (hv : ∀ ρ, V G ρ = 1 + TV (cross ρ) / 2) : ∀ σ, V G (law G σ) ≤ V G (law G truth) := by
  intro σ
  have hl : cross (law G σ) =
      post (cross (law G truth)) (σ 0) (σ 1) := by
    simpa [truth, PMF.pure_bind] using cross_law_post G truth σ
  have hb := data_processing (cross (law G truth)) (σ 0) (σ 1)
  rw [← hl] at hb
  simp only [hv, TV_eq]
  linarith

/-- Both-worker data processing is proved for these payoffs, not assumed in TwoPairOutcome. -/
theorem truth_value_maximal :
    (∀ σ, V (bonusGame P f) (law (bonusGame P f) σ) ≤
      V (bonusGame P f) (law (bonusGame P f) truth)) ∧
    (∀ σ, V (mediatedGame P f) (law (mediatedGame P f) σ) ≤
      V (mediatedGame P f) (law (mediatedGame P f) truth)) :=
  ⟨maximal_of_envelope _ (fun ρ => (values P f ρ).1),
    maximal_of_envelope _ (fun ρ => (values P f ρ).2)⟩



end MutualEvaluation.Timing
end