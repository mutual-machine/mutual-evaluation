import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Internal.ReplicationInformation

/-!
INTERNAL — consequences for the actual replication scores.

The equalities used below were proved from the original stream experiment,
including integrability and the invalid-critic branch. They are not hypotheses
or replacements for the loop integrals.

These are channel-level conclusions for one fixed reporting kernel per
experiment. They do not assert TwoPairOutcome.robustness, uniqueness, semantic correctness,
or protection against within-loop adaptive reporting.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.Replication
open Binary Probability FiniteTask

variable {X R : Type} [Fintype X] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
variable (P : PMF X) (k : Kernel X R)

/-- Transfer over the full critic space, including invalid critics. -/
theorem V_chiSquared_eq_target :
    rp_Replication_V_chiSquared P k = PearsonTarget.value P k := by
  change sSup (Set.range fun c : Critic R => rp_Replication_u_chiSquared c P k) =
    sSup (Set.range fun c : Critic R => PearsonTarget.payoff c P k)
  simp_rw [u_chiSquared_eq_target]

theorem V_KL_eq_target :
    rp_Replication_V_KL P k = ShannonTarget.value P k := by
  change sSup (Set.range fun c : Critic R => rp_Replication_u_KL c P k) =
    sSup (Set.range fun c : Critic R => ShannonTarget.payoff c P k)
  simp_rw [u_KL_eq_target]

theorem r_chiSquared_eq_target (c : Critic R) :
    rp_Replication_r_chiSquared c P k = PearsonTarget.regret c P k := by
  exact congrArg₂ (fun a b : ℝ => a - b)
    (V_chiSquared_eq_target P k) (u_chiSquared_eq_target c P k)

theorem r_KL_eq_target (c : Critic R) :
    rp_Replication_r_KL c P k = ShannonTarget.regret c P k := by
  exact congrArg₂ (fun a b : ℝ => a - b)
    (V_KL_eq_target P k) (u_KL_eq_target c P k)

/-- The actual Pearson loop envelope is full task/report information. -/
theorem V_chiSquared_eq_impl : rp_Replication_V_chiSquared P k = rp_FiniteTask_pearson P k :=
  (V_chiSquared_eq_target P k).trans (PearsonTarget.value_eq P k)

/-- The actual harmonic loop envelope is Shannon information in nats. -/
theorem V_KL_eq_impl : rp_Replication_V_KL P k = rp_FiniteTask_shannon P k :=
  (V_KL_eq_target P k).trans (ShannonTarget.value_eq P k)

omit [MeasurableSpace R] [MeasurableSingletonClass R] in
private theorem taskReport_independent_iff_posterior :
    independent (jointLaw P PMF.pure k) ↔
      ∀ a, 0 < rp_FiniteTask_reportMass P k a → rp_FiniteTask_posterior P k a = mass P := by
  classical
  let q := P.bind fun x => (k x).map fun a => (x, a)
  have hq : jointLaw P PMF.pure k = q := by
    simp only [jointLaw, pair, PMF.pure_bind, q]
  have hfst : q.map Prod.fst = P := by
    simp only [q, PMF.map_bind, PMF.map_comp]
    change (P.bind fun x => (k x).map (Function.const R x)) = P
    simp [PMF.map_const, PMF.bind_pure]
  have hsnd : q.map Prod.snd = P.bind k := by
    simp only [q, PMF.map_bind, PMF.map_comp]
    change (P.bind fun x => (k x).map id) = P.bind k
    simp [PMF.map_id]
  have hjoint (x : X) (a : R) : mass q (x, a) = rp_FiniteTask_jointMass P k x a := by
    change mass (P.bind fun y => (k y).bind fun b => PMF.pure (y, b)) (x, a) =
      mass P x * mass (k x) a
    simp [mass_bind, mass_pure, Prod.mk.injEq, ite_and]
  have hi : independent q ↔ ∀ x a,
      rp_FiniteTask_jointMass P k x a = mass P x * rp_FiniteTask_reportMass P k a := by
    rw [independent_iff_mass, hfst, hsnd]
    simp_rw [hjoint]
  rw [hq, hi]
  constructor
  · intro h a ha
    funext x
    change rp_FiniteTask_jointMass P k x a / rp_FiniteTask_reportMass P k a = mass P x
    rw [h x a, mul_div_cancel_right₀ _ (ne_of_gt ha)]
  · intro h x a
    by_cases ha : rp_FiniteTask_reportMass P k a = 0
    · rw [jointMass_zero_of_reportMass_zero P k x a ha]
      rw [ha, mul_zero]
    · rw [← weighted_posterior, h a (lt_of_le_of_ne (reportMass_nonneg P k a) (Ne.symm ha))]
      exact mul_comm _ _

omit [Fintype X] [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] in
private theorem constant_annotation_posterior (b : Unit) :
    rp_FiniteTask_posterior P (rp_FiniteTask_annotated k (fun _ : R => ())) b = mass P := by
  cases b
  funext x
  have hchannel : rp_FiniteTask_annotated k (fun _ : R => ()) = fun _ => PMF.pure () := by
    funext y
    exact PMF.map_const _ _
  rw [hchannel]
  simp [mass, PMF.bind_const]

omit [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] in
private theorem constant_annotation_information :
    rp_FiniteTask_pearson P (rp_FiniteTask_annotated k (fun _ : R => ())) = 0 ∧
      rp_FiniteTask_shannon P (rp_FiniteTask_annotated k (fun _ : R => ())) = 0 := by
  constructor
  · rw [pearson_eq_posterior]
    apply Finset.sum_eq_zero
    intro x _
    rw [Fintype.sum_unique]
    let k' : Kernel X Unit := rp_FiniteTask_annotated k (fun _ : R => ())
    change rp_FiniteTask_reportMass P k' () *
      (rp_FiniteTask_posterior P k' () x - mass P x)^2 / mass P x = 0
    have hpost : rp_FiniteTask_posterior P k' () x = mass P x :=
      congrFun (constant_annotation_posterior P k ()) x
    rw [hpost]
    simp
  · rw [shannon_eq_posterior]
    apply Finset.sum_eq_zero
    intro b _
    let k' : Kernel X Unit := rp_FiniteTask_annotated k (fun _ : R => ())
    change rp_FiniteTask_reportMass P k' b *
      rp_FiniteLog_divergence (rp_FiniteTask_posterior P k' b) (mass P) = 0
    have hpost : rp_FiniteTask_posterior P k' b = mass P := constant_annotation_posterior P k b
    rw [hpost, FiniteLog.divergence_self, mul_zero]

theorem V_chiSquared_zero_iff_independent_impl :
    rp_Replication_V_chiSquared P k = 0 ↔
      independent (jointLaw P PMF.pure k) := by
  rw [V_chiSquared_eq_impl, ← (constant_annotation_information P k).1, pearson_annotation_eq_iff]
  simpa only [constant_annotation_posterior] using (taskReport_independent_iff_posterior P k).symm

theorem V_KL_zero_iff_independent_impl :
    rp_Replication_V_KL P k = 0 ↔
      independent (jointLaw P PMF.pure k) := by
  rw [V_KL_eq_impl, ← (constant_annotation_information P k).2, shannon_annotation_eq_iff]
  simpa only [constant_annotation_posterior] using (taskReport_independent_iff_posterior P k).symm

theorem u_chiSquared_literal :
    rp_Replication_u_chiSquared (rp_Binary_annotate id) P k = rp_FiniteTask_pearson P k :=
  (u_chiSquared_eq_target _ P k).trans (PearsonTarget.literal_payoff P k)

theorem u_KL_literal :
    rp_Replication_u_KL (rp_Binary_annotate id) P k = rp_FiniteTask_shannon P k :=
  (u_KL_eq_target _ P k).trans (ShannonTarget.literal_payoff P k)

theorem chiSquared_literal_optimal_impl :
    rp_Replication_u_chiSquared (rp_Binary_annotate id) P k = rp_Replication_V_chiSquared P k :=
  (u_chiSquared_literal P k).trans (MutualEvaluation.Replication.V_chiSquared_eq_impl P k).symm

theorem kl_literal_optimal_impl :
    rp_Replication_u_KL (rp_Binary_annotate id) P k = rp_Replication_V_KL P k :=
  (u_KL_literal P k).trans (MutualEvaluation.Replication.V_KL_eq_impl P k).symm

theorem u_chiSquared_nonneg (c : Critic R) : 0 ≤ rp_Replication_u_chiSquared c P k := by
  rw [u_chiSquared_eq_target]
  exact PearsonTarget.payoff_nonneg P k c

theorem u_KL_nonneg (c : Critic R) : 0 ≤ rp_Replication_u_KL c P k := by
  rw [u_KL_eq_target]
  exact ShannonTarget.payoff_nonneg P k c

theorem u_chiSquared_le_value_impl (c : Critic R) :
    rp_Replication_u_chiSquared c P k ≤ rp_Replication_V_chiSquared P k := by
  rw [u_chiSquared_eq_target, MutualEvaluation.Replication.V_chiSquared_eq_impl]
  exact PearsonTarget.payoff_le_information P k c

theorem u_KL_le_value_impl (c : Critic R) :
    rp_Replication_u_KL c P k ≤ rp_Replication_V_KL P k := by
  rw [u_KL_eq_target, MutualEvaluation.Replication.V_KL_eq_impl]
  exact ShannonTarget.payoff_le_information P k c

theorem r_chiSquared_nonneg (c : Critic R) : 0 ≤ rp_Replication_r_chiSquared c P k := by
  rw [r_chiSquared_eq_target]
  exact PearsonTarget.regret_nonneg P k c

theorem r_KL_nonneg (c : Critic R) : 0 ≤ rp_Replication_r_KL c P k := by
  rw [r_KL_eq_target]
  exact ShannonTarget.regret_nonneg P k c

omit [Fintype R] [MeasurableSingletonClass R] in
theorem r_chiSquared_zero_iff (c : Critic R) :
    rp_Replication_r_chiSquared c P k = 0 ↔ rp_Replication_u_chiSquared c P k = rp_Replication_V_chiSquared P k := by
  rw [ sub_eq_zero, eq_comm]

omit [Fintype R] [MeasurableSingletonClass R] in
theorem r_KL_zero_iff (c : Critic R) :
    rp_Replication_r_KL c P k = 0 ↔ rp_Replication_u_KL c P k = rp_Replication_V_KL P k := by
  rw [ sub_eq_zero, eq_comm]

/-- Posterior squared loss is the regret of the actual collision payment.
Real division makes null prior coordinates contribute zero. -/
theorem r_chiSquared_annotation_impl {B : Type} [Fintype B] (g : R → B) :
    rp_Replication_r_chiSquared (rp_Binary_annotate g) P k =
      ∑ x, (∑ a, rp_FiniteTask_reportMass P k a *
        (rp_FiniteTask_posterior P k a x - rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a) x)^2) /
          mass P x := by
  rw [r_chiSquared_eq_target]
  exact PearsonTarget.annotation_regret P k g

/-- Conditional information is the regret of the actual harmonic payment. -/
theorem r_KL_annotation_impl {B : Type} [Fintype B] (g : R → B) :
    rp_Replication_r_KL (rp_Binary_annotate g) P k = rp_FiniteTask_conditionalInformation P k g := by
  rw [r_KL_eq_target]
  exact ShannonTarget.annotation_regret P k g

/-- Sufficiency concerns positive-mass reports, not global critic validity. -/
theorem chiSquared_annotation_zero_iff_impl {B : Type} [Fintype B] (g : R → B) :
    rp_Replication_r_chiSquared (rp_Binary_annotate g) P k = 0 ↔
      ∀ a, 0 < rp_FiniteTask_reportMass P k a →
        rp_FiniteTask_posterior P k a = rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a) := by
  rw [r_chiSquared_eq_target]
  exact PearsonTarget.annotation_zero_iff P k g

theorem kl_annotation_zero_iff_impl {B : Type} [Fintype B] (g : R → B) :
    rp_Replication_r_KL (rp_Binary_annotate g) P k = 0 ↔
      ∀ a, 0 < rp_FiniteTask_reportMass P k a →
        rp_FiniteTask_posterior P k a = rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a) := by
  rw [r_KL_eq_target]
  exact ShannonTarget.annotation_zero_iff P k g

theorem chiSquared_annotation_optimal_iff {B : Type} [Fintype B] (g : R → B) :
    rp_Replication_u_chiSquared (rp_Binary_annotate g) P k = rp_Replication_V_chiSquared P k ↔
      ∀ a, 0 < rp_FiniteTask_reportMass P k a →
        rp_FiniteTask_posterior P k a = rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a) :=
  (r_chiSquared_zero_iff P k (rp_Binary_annotate g)).symm.trans
    (MutualEvaluation.Replication.chiSquared_annotation_zero_iff_impl P k g)

theorem kl_annotation_optimal_iff {B : Type} [Fintype B] (g : R → B) :
    rp_Replication_u_KL (rp_Binary_annotate g) P k = rp_Replication_V_KL P k ↔
      ∀ a, 0 < rp_FiniteTask_reportMass P k a →
        rp_FiniteTask_posterior P k a = rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a) :=
  (r_KL_zero_iff P k (rp_Binary_annotate g)).symm.trans (MutualEvaluation.Replication.kl_annotation_zero_iff_impl P k g)

theorem chiSquared_critic_coarsening_impl {B C : Type} [Fintype B] [Fintype C]
    (g : R → B) (h : B → C) :
    rp_Replication_u_chiSquared (rp_Binary_annotate (h ∘ g)) P k ≤ rp_Replication_u_chiSquared (rp_Binary_annotate g) P k := by
  exact (u_chiSquared_eq_target (rp_Binary_annotate (h ∘ g)) P k).trans_le
    ((PearsonTarget.critic_coarsening P k g h).trans_eq
      (u_chiSquared_eq_target (rp_Binary_annotate g) P k).symm)

theorem kl_critic_coarsening_impl {B C : Type} [Fintype B] [Fintype C]
    (g : R → B) (h : B → C) :
    rp_Replication_u_KL (rp_Binary_annotate (h ∘ g)) P k ≤ rp_Replication_u_KL (rp_Binary_annotate g) P k := by
  exact (u_KL_eq_target (rp_Binary_annotate (h ∘ g)) P k).trans_le
    ((ShannonTarget.critic_coarsening P k g h).trans_eq
      (u_KL_eq_target (rp_Binary_annotate g) P k).symm)

theorem V_chiSquared_data_processing_impl {B : Type} [Fintype B]
    [MeasurableSpace B] [MeasurableSingletonClass B] (τ : Kernel R B) :
    rp_Replication_V_chiSquared P (fun x => (k x).bind τ) ≤ rp_Replication_V_chiSquared P k := by
  rw [MutualEvaluation.Replication.V_chiSquared_eq_impl, MutualEvaluation.Replication.V_chiSquared_eq_impl]
  exact pearson_data_processing P k τ

theorem V_KL_data_processing_impl {B : Type} [Fintype B]
    [MeasurableSpace B] [MeasurableSingletonClass B] (τ : Kernel R B) :
    rp_Replication_V_KL P (fun x => (k x).bind τ) ≤ rp_Replication_V_KL P k := by
  rw [MutualEvaluation.Replication.V_KL_eq_impl, MutualEvaluation.Replication.V_KL_eq_impl]
  exact shannon_data_processing P k τ

theorem V_chiSquared_robust_impl (τ : Kernel R R) :
    robustUnderGarbling (rp_Replication_V_chiSquared P) (jointLaw P Kernel.truth)
      Kernel.garble k τ := by
  refine ⟨V_chiSquared_data_processing_impl P k τ, fun hbefore hafter => ?_⟩
  have hnonneg : 0 ≤ rp_Replication_V_chiSquared P k := by
    rw [V_chiSquared_eq_impl]
    exact pearson_nonneg P k
  exact ((V_chiSquared_zero_iff_independent_impl P (k.garble τ)).2 hafter).trans_lt <|
    lt_of_le_of_ne hnonneg fun hzero =>
      hbefore ((V_chiSquared_zero_iff_independent_impl P k).1 hzero.symm)

theorem V_KL_robust_impl (τ : Kernel R R) :
    robustUnderGarbling (rp_Replication_V_KL P) (jointLaw P Kernel.truth)
      Kernel.garble k τ := by
  refine ⟨V_KL_data_processing_impl P k τ, fun hbefore hafter => ?_⟩
  have hnonneg : 0 ≤ rp_Replication_V_KL P k := by
    rw [V_KL_eq_impl]
    exact shannon_nonneg P k
  exact ((V_KL_zero_iff_independent_impl P (k.garble τ)).2 hafter).trans_lt <|
    lt_of_le_of_ne hnonneg fun hzero =>
      hbefore ((V_KL_zero_iff_independent_impl P k).1 hzero.symm)

/-- Any truthful-channel optimizer bounds every simultaneous change of critic
and fixed reporting kernel, for the original Pearson loop score. -/
theorem chiSquared_truthful_global_optimal_impl (c : Critic R)
    (hc : rp_Replication_u_chiSquared c P k = rp_Replication_V_chiSquared P k)
    (d : Critic R) (σ : Kernel R R) :
    rp_Replication_u_chiSquared d P (fun x => (k x).bind σ) ≤ rp_Replication_u_chiSquared c P k := by
  rw [u_chiSquared_eq_target, V_chiSquared_eq_target] at hc
  simpa only [u_chiSquared_eq_target] using
    PearsonTarget.truthful_global_optimal P k c hc d σ

theorem kl_truthful_global_optimal_impl (c : Critic R)
    (hc : rp_Replication_u_KL c P k = rp_Replication_V_KL P k)
    (d : Critic R) (σ : Kernel R R) :
    rp_Replication_u_KL d P (fun x => (k x).bind σ) ≤ rp_Replication_u_KL c P k := by
  rw [u_KL_eq_target, V_KL_eq_target] at hc
  simpa only [u_KL_eq_target] using
    ShannonTarget.truthful_global_optimal P k c hc d σ

/-- Both unilateral best-response inequalities for one worker and one critic.
Worker deviations select a reporting kernel before sampling begins. -/
theorem chiSquared_truthful_best_responses (c : Critic R)
    (hc : rp_Replication_u_chiSquared c P k = rp_Replication_V_chiSquared P k) :
    (∀ d, rp_Replication_u_chiSquared d P k ≤ rp_Replication_u_chiSquared c P k) ∧
      ∀ σ : Kernel R R,
        rp_Replication_u_chiSquared c P (fun x => (k x).bind σ) ≤ rp_Replication_u_chiSquared c P k := by
  rw [u_chiSquared_eq_target, V_chiSquared_eq_target] at hc
  simpa only [u_chiSquared_eq_target] using
    PearsonTarget.truthful_best_responses P k c hc

theorem kl_truthful_best_responses (c : Critic R)
    (hc : rp_Replication_u_KL c P k = rp_Replication_V_KL P k) :
    (∀ d, rp_Replication_u_KL d P k ≤ rp_Replication_u_KL c P k) ∧
      ∀ σ : Kernel R R, rp_Replication_u_KL c P (fun x => (k x).bind σ) ≤ rp_Replication_u_KL c P k := by
  rw [u_KL_eq_target, V_KL_eq_target] at hc
  simpa only [u_KL_eq_target] using
    ShannonTarget.truthful_best_responses P k c hc

/-- Relabeling need only be injective; unused annotation labels do not matter. -/
theorem chiSquared_injective_annotation {B : Type} [Fintype B]
    (g : R → B) (hg : Function.Injective g) :
    rp_Replication_u_chiSquared (rp_Binary_annotate g) P k = rp_Replication_V_chiSquared P k ∧
      rp_Replication_r_chiSquared (rp_Binary_annotate g) P k = 0 := by
  have he : rp_Replication_u_chiSquared (rp_Binary_annotate g) P k = rp_Replication_V_chiSquared P k := by
    rw [MutualEvaluation.Replication.u_chiSquared_annotation_impl, MutualEvaluation.Replication.V_chiSquared_eq_impl]
    exact pearson_annotation_injective P k g hg
  exact ⟨he, (r_chiSquared_zero_iff P k (rp_Binary_annotate g)).2 he⟩

theorem kl_injective_annotation {B : Type} [Fintype B]
    (g : R → B) (hg : Function.Injective g) :
    rp_Replication_u_KL (rp_Binary_annotate g) P k = rp_Replication_V_KL P k ∧ rp_Replication_r_KL (rp_Binary_annotate g) P k = 0 := by
  have he : rp_Replication_u_KL (rp_Binary_annotate g) P k = rp_Replication_V_KL P k := by
    rw [MutualEvaluation.Replication.u_KL_annotation_impl, MutualEvaluation.Replication.V_KL_eq_impl]
    exact shannon_annotation_injective P k g hg
  exact ⟨he, (r_KL_zero_iff P k (rp_Binary_annotate g)).2 he⟩

end MutualEvaluation.Replication
end