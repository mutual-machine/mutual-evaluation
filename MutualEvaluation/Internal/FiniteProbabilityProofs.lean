import MutualEvaluation.Public.TwoPairOutcome

/-! INTERNAL — implementation and proof support; not an author-certified annotation file. -/

/-! Shared probability proofs for the paper constructions; no model assumptions. -/
noncomputable section
namespace MutualEvaluation.Probability

/- Local syntax expands to Core/Mathlib expressions; it declares no mass function. -/
local notation "mass" => (fun {A : Type} (p : PMF A) (a : A) => ENNReal.toReal (p a))

namespace Proofs

theorem mass_nonneg {A : Type} (p : PMF A) (a : A) : 0 ≤ mass p a :=
  ENNReal.toReal_nonneg

theorem mass_le_one {A : Type} (p : PMF A) (a : A) : mass p a ≤ 1 := by
  simpa only [ENNReal.toReal_one] using
    (ENNReal.toReal_le_toReal (p.apply_ne_top a) ENNReal.one_ne_top).2 (p.coe_le_one a)

theorem mass_sum {A : Type} [Fintype A] (p : PMF A) : ∑ a, mass p a = 1 := by
  have h := congrArg ENNReal.toReal p.tsum_coe
  rw [tsum_fintype, ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)] at h
  exact h

theorem mass_bind {A B : Type} [Fintype A] (p : PMF A) (k : Kernel A B) (b : B) :
    mass (p.bind k) b = ∑ a, mass p a * mass (k a) b := by
  simp only [PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top
    (p.apply_ne_top a) ((k a).apply_ne_top b))]
  simp only [ENNReal.toReal_mul]

theorem mass_pure {A : Type} [DecidableEq A] (a b : A) :
    mass (PMF.pure a) b = if b = a then 1 else 0 := by
  by_cases h : b = a <;> simp [PMF.pure_apply, h]

theorem mass_pair {A B : Type} [Fintype A] [Fintype B]
    (p : PMF A) (q : PMF B) (a : A) (b : B) :
    mass (pair p q) (a, b) = mass p a * mass q b := by
  classical
  change mass (p.bind fun x => q.bind fun y => PMF.pure (x, y)) (a, b) = _
  simp only [mass_bind, mass_pure, Prod.mk.injEq]
  simp [ite_and]

theorem independent_iff_mass {A B : Type} (μ : PMF (A × B)) :
    independent μ ↔ ∀ a b,
      mass μ (a, b) = mass (μ.map Prod.fst) a * mass (μ.map Prod.snd) b := by
  constructor
  · intro h a b
    simpa only [ENNReal.toReal_mul] using congrArg ENNReal.toReal (h a b)
  · intro h a b
    have he := congrArg ENNReal.ofReal (h a b)
    simpa only [← ENNReal.toReal_mul,
      ENNReal.ofReal_toReal (μ.apply_ne_top (a, b)),
      ENNReal.ofReal_toReal (ENNReal.mul_ne_top
        ((μ.map Prod.fst).apply_ne_top a) ((μ.map Prod.snd).apply_ne_top b))] using he

end Proofs

/-- Independent local post-processing of a pair, not a vector reporting policy. -/
def post {A B C D : Type} (μ : PMF (A × B)) (κ : Kernel A C) (η : Kernel B D) :
    PMF (C × D) := μ.bind fun ab => pair (κ ab.1) (η ab.2)

namespace Proofs

theorem mass_post {A B C D : Type} [Fintype A] [Fintype B]
    [Fintype C] [Fintype D] (μ : PMF (A × B)) (κ : Kernel A C) (η : Kernel B D)
    (c : C) (d : D) :
    mass (post μ κ η) (c, d) =
      ∑ a, ∑ b, mass μ (a, b) * mass (κ a) c * mass (η b) d := by
  simp only [post, mass_bind, mass_pair, Fintype.sum_prod_type, mul_assoc]

end Proofs

theorem pair_bind {A B C D : Type} (p : PMF A) (q : PMF B)
    (κ : Kernel A C) (η : Kernel B D) :
    pair (p.bind κ) (q.bind η) = post (pair p q) κ η := by
  simp only [pair, post, PMF.bind_bind, PMF.map_bind, PMF.bind_map, Function.comp_def]
  congr 1
  funext a
  exact PMF.bind_comm _ _ _

/-- Integrates out the two unused replicas of the outcome. -/
theorem cross_law {X R : Type} (G : Game X R) (σ : Fin 2 → Kernel R R) :
    cross (law G σ) =
      G.P.bind fun x => pair ((G.w 0 x).bind (σ 0)) ((G.w 1 x).bind (σ 1)) := by
  simp only [cross, law, jointLaw, Kernel.replicate, Kernel.garble, pair, PMF.map, Function.comp_def,
    PMF.bind_bind, PMF.pure_bind, PMF.bind_const]

/-- Both local reporting compositions, with no finite-alphabet hypothesis. -/
theorem cross_law_post {X R : Type} (G : Game X R)
    (σ τ : Fin 2 → Kernel R R) :
    cross (law G (fun i a => (σ i a).bind (τ i))) =
      post (cross (law G σ)) (τ 0) (τ 1) := by
  rw [cross_law, cross_law]
  unfold post
  rw [PMF.bind_bind]
  congr 1
  funext x
  rw [← PMF.bind_bind, ← PMF.bind_bind]
  exact pair_bind _ _ _ _

/-- Reporter 0's self pair; the peer's channel and reporting policy disappear. -/
theorem self_law {X R : Type} (G : Game X R) (σ : Fin 2 → Kernel R R) :
    (law G σ).map Prod.fst =
      G.P.bind fun x => pair ((G.w 0 x).bind (σ 0)) ((G.w 0 x).bind (σ 0)) := by
  simp only [law, jointLaw, Kernel.replicate, Kernel.garble, pair, PMF.map, Function.comp_def,
    PMF.bind_bind, PMF.pure_bind, PMF.bind_const]

end MutualEvaluation.Probability
end