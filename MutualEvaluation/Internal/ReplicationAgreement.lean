import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Internal.ReplicationInformation
import MutualEvaluation.Internal.SelfAgreement

/-!
INTERNAL — Pearson's normalized-agreement and pair-law implementation bridge.

The existing Self.Q, Self.H, and Self.agreement definitions are reused.
Unlike the earlier fair-binary information calculation, these identities allow
any finite task prior and reported channel. Null denominators contribute zero.

The loop expectation is still the original Bochner integral. Its factorization
through the same-task pair law is proved, including the invalid-critic branch.
No analogous fixed-length-law factorization is asserted for KL.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.Replication
open Probability Binary FiniteTask
attribute [local instance] Classical.propDecidable

section PairAlgebra
variable {X R : Type}

theorem sameTaskPair_fst (P : PMF X) (k : Kernel X R) :
    (P.bind fun x => pair (k x) (k x)).map Prod.fst = P.bind k := by
  simp only [pair, PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind,
    PMF.bind_const, PMF.bind_pure]

variable [Fintype X] [Fintype R]

theorem sameTaskPair_mass (P : PMF X) (k : Kernel X R) (a b : R) :
    mass (P.bind fun x => pair (k x) (k x)) (a, b) =
      ∑ x, mass P x * mass (k x) a * mass (k x) b := by
  rw [mass_bind]
  simp only [mass_pair, mul_assoc]

/-- The existing normalized-agreement numerator under general same-task
replication. The critic need not be valid for this finite-law identity. -/
theorem sameTaskPair_H (P : PMF X) (k : Kernel X R) (c : Critic R) (a : R) :
    Self.H c (P.bind fun x => pair (k x) (k x)) a =
      ∑ x, mass P x * mass (k x) a *
        (∑ b, if rp_Binary_Rel c a b then mass (k x) b else 0) := by
  unfold Self.H
  simp_rw [sameTaskPair_mass]
  calc
    _ = ∑ b, ∑ x, if rp_Binary_Rel c a b then
        mass P x * mass (k x) a * mass (k x) b else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : rp_Binary_Rel c a b <;> simp [hb]
    _ = ∑ x, ∑ b, if rp_Binary_Rel c a b then
        mass P x * mass (k x) a * mass (k x) b else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : rp_Binary_Rel c a b <;> simp [hb]

/-- General Pearson information as a same-task collision ratio.
The two reports are independent conditional on the same task, not fresh tasks.
The total real division convention handles null reports. -/
theorem pearson_eq_collision_ratio (P : PMF X) (k : Kernel X R) :
    rp_FiniteTask_pearson P k =
      (∑ a, mass (P.bind fun x => pair (k x) (k x)) (a, a) /
        rp_FiniteTask_reportMass P k a) - 1 := by
  rw [pearson_channel_sum]
  apply congrArg (fun z : ℝ => z - 1)
  simp only [sameTaskPair_mass, Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro x _
  ring

end PairAlgebra

section Implementation
variable {X R : Type} [Fintype X] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]

/-- The actual collision-gated Pearson expectation equals the existing
normalized-agreement functional for every globally valid critic. -/
theorem u_chiSquared_agreement (c : Critic R) (hc : rp_Binary_Valid c)
    (P : PMF X) (k : Kernel X R) :
    rp_Replication_u_chiSquared c P k =
      Self.agreement c (P.bind fun x => pair (k x) (k x)) := by
  have hQ (a : R) :
      Self.Q c (P.bind fun x => pair (k x) (k x)) a =
        ((P.bind k).toMeasure {b | rp_Binary_Rel c a b}).toReal := by
    simp only [Self.Q, sameTaskPair_fst, toMeasure_real_sum, Set.mem_ofPred_eq]
  have hH (a : R) :
      Self.H c (P.bind fun x => pair (k x) (k x)) a =
        ∑ x, mass P x * mass (k x) a *
          ((k x).toMeasure {b | rp_Binary_Rel c a b}).toReal := by
    rw [sameTaskPair_H]
    simp only [toMeasure_real_sum, Set.mem_ofPred_eq]
  rw [u_chiSquared_class_sum c hc P k, Self.agreement]
  simp_rw [hQ, hH]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, mass_sum]
  apply congrArg (fun z : ℝ => z - 1)
  simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

/-- Factorization on the entire binary critic space; validity remains a
payment branch rather than a restriction of the critic's strategy space. -/
theorem u_chiSquared_pair_law (c : Critic R) (P : PMF X) (k : Kernel X R) :
    rp_Replication_u_chiSquared c P k =
      if rp_Binary_Valid c then Self.agreement c (P.bind fun x => pair (k x) (k x))
      else 0 := by
  by_cases hc : rp_Binary_Valid c
  · rw [if_pos hc]
    exact u_chiSquared_agreement c hc P k
  · rw [if_neg hc, (MutualEvaluation.Replication.invalid_scores_impl c hc P k).1]

/-- Equal same-task pair laws give equal actual Pearson scores, even if their
latent task alphabets differ. No such assertion is made for the KL score. -/
theorem u_chiSquared_eq_of_pair_law_eq {Z : Type} [Fintype Z]
    (P : PMF X) (k : Kernel X R) (Q : PMF Z) (l : Kernel Z R)
    (he : (P.bind fun x => pair (k x) (k x)) =
      (Q.bind fun z => pair (l z) (l z))) (c : Critic R) :
    rp_Replication_u_chiSquared c P k = rp_Replication_u_chiSquared c Q l := by
  rw [u_chiSquared_pair_law, u_chiSquared_pair_law, he]

/-- Explicit correspondence with TwoPairOutcome's primary-worker self-pair projection.
This is a payoff identity, not a TwoPairOutcome robustness certificate. -/
theorem u_chiSquared_core_law (G : Game X R)
    (σ : Fin 2 → Kernel R R) (c : Critic R) :
    rp_Replication_u_chiSquared c G.P (fun x => (G.w 0 x).bind (σ 0)) =
      if rp_Binary_Valid c then Self.agreement c ((law G σ).map Prod.fst) else 0 := by
  have hp : (law G σ).map Prod.fst =
      G.P.bind fun x =>
        pair ((G.w 0 x).bind (σ 0)) ((G.w 0 x).bind (σ 0)) := by
    simp only [law, jointLaw, Kernel.replicate, Kernel.garble, pair, PMF.map, Function.comp_def, PMF.bind_bind,
      PMF.pure_bind, PMF.bind_const]
  rw [hp, u_chiSquared_pair_law]

/-- The manuscript's annotation collision-ratio identity for the actual loop.
The annotation alphabet needs no measurable-space structure. -/
theorem u_chiSquared_collision_ratio_impl {B : Type} [Fintype B]
    (P : PMF X) (k : Kernel X R) (g : R → B) :
    rp_Replication_u_chiSquared (rp_Binary_annotate g) P k =
      (∑ b, mass (P.bind fun x =>
          pair (rp_FiniteTask_annotated k g x) (rp_FiniteTask_annotated k g x)) (b, b) /
        rp_FiniteTask_reportMass P (rp_FiniteTask_annotated k g) b) - 1 :=
  (MutualEvaluation.Replication.u_chiSquared_annotation_impl P k g).trans
    (pearson_eq_collision_ratio P (rp_FiniteTask_annotated k g))

/-- The existing normalized-agreement functional retains exactly annotation
information for arbitrary finite tasks, extending the earlier fair-bit result. -/
theorem annotation_agreement_information {B : Type} [Fintype B]
    (P : PMF X) (k : Kernel X R) (g : R → B) :
    Self.agreement (rp_Binary_annotate g) (P.bind fun x => pair (k x) (k x)) =
      rp_FiniteTask_pearson P (rp_FiniteTask_annotated k g) :=
  (u_chiSquared_agreement (rp_Binary_annotate g) (MutualEvaluation.Binary.annotate_valid_impl g) P k).symm.trans
    (MutualEvaluation.Replication.u_chiSquared_annotation_impl P k g)

end Implementation
end MutualEvaluation.Replication
end