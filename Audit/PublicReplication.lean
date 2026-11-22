import MutualEvaluation.Public.Replication

/-!
Technical inspection of the 70 declarations in Public/Replication.
Public declarations and author annotations live in that module.
This batch is not an annotation or an additional mathematical assumption.
Source ownership and audit coverage are checked by scripts/check_annotations.py.
Computational annotation closure is checked by scripts/check_interface.py.
-/

#print MutualEvaluation.Binary.Rel
#print MutualEvaluation.Binary.Valid
#print MutualEvaluation.Binary.annotate
#check @MutualEvaluation.Binary.annotate_valid
#check @MutualEvaluation.Binary.valid_iff_annotation
#print MutualEvaluation.Replication.SampleSpace
#print MutualEvaluation.Replication.Transcript
#print MutualEvaluation.Replication.iid
#print MutualEvaluation.Replication.conditionalTranscriptLaw
#print MutualEvaluation.Replication.transcriptLaw
#print MutualEvaluation.Replication.firstHit
#print MutualEvaluation.Replication.R_specific
#print MutualEvaluation.Replication.R_null
#check @MutualEvaluation.Replication.annotation_clocks
#print MutualEvaluation.Replication.W_chiSquared
#print MutualEvaluation.Replication.H
#print MutualEvaluation.Replication.W_KL
#print MutualEvaluation.Replication.u_chiSquared
#print MutualEvaluation.Replication.u_KL
#print MutualEvaluation.Replication.pearsonScore
#print MutualEvaluation.Replication.klScore
#print MutualEvaluation.Replication.V_chiSquared
#print MutualEvaluation.Replication.V_KL
#print MutualEvaluation.Replication.r_chiSquared
#print MutualEvaluation.Replication.r_KL
#check @MutualEvaluation.Replication.invalid_scores
#print MutualEvaluation.FiniteTask.annotated
#print MutualEvaluation.FiniteTask.jointMass
#print MutualEvaluation.FiniteTask.reportMass
#print MutualEvaluation.FiniteTask.pearson
#print MutualEvaluation.FiniteTask.shannon
#check @MutualEvaluation.Replication.termination
#check @MutualEvaluation.Replication.integrable_W_chiSquared
#check @MutualEvaluation.Replication.integrable_W_KL
#check @MutualEvaluation.Replication.u_chiSquared_annotation
#check @MutualEvaluation.Replication.u_KL_annotation
#check @MutualEvaluation.Replication.u_chiSquared_collision_ratio
#print MutualEvaluation.FiniteTask.posterior
#print MutualEvaluation.FiniteLog.divergence
#print MutualEvaluation.FiniteTask.conditionalInformation
#check @MutualEvaluation.Replication.V_chiSquared_eq
#check @MutualEvaluation.Replication.V_KL_eq
#check @MutualEvaluation.Replication.chiSquared_literal_optimal
#check @MutualEvaluation.Replication.kl_literal_optimal
#check @MutualEvaluation.Replication.r_chiSquared_annotation
#check @MutualEvaluation.Replication.r_KL_annotation
#check @MutualEvaluation.Replication.chiSquared_annotation_zero_iff
#check @MutualEvaluation.Replication.kl_annotation_zero_iff
#check @MutualEvaluation.Replication.chiSquared_critic_coarsening
#check @MutualEvaluation.Replication.kl_critic_coarsening
#check @MutualEvaluation.Replication.u_chiSquared_le_value
#check @MutualEvaluation.Replication.u_KL_le_value
#check @MutualEvaluation.Replication.V_chiSquared_data_processing
#check @MutualEvaluation.Replication.V_KL_data_processing
#check @MutualEvaluation.Replication.chiSquared_truthful_global_optimal
#check @MutualEvaluation.Replication.kl_truthful_global_optimal
#print MutualEvaluation.Replication.reportingNash
#check @MutualEvaluation.Replication.chiSquared_truthful_nash
#check @MutualEvaluation.Replication.kl_truthful_nash
#print MutualEvaluation.Self.fair
#print MutualEvaluation.Self.Nuisance.worker
#print MutualEvaluation.Self.Nuisance.literal
#print MutualEvaluation.Self.Nuisance.task
#print MutualEvaluation.Self.Nuisance.constant
#check @MutualEvaluation.Replication.Example.chiSquared_payoff_table
#check @MutualEvaluation.Replication.Example.kl_payoff_table
#check @MutualEvaluation.Replication.Example.chiSquared_regret_table
#check @MutualEvaluation.Replication.Example.kl_regret_table
#check @MutualEvaluation.Replication.Example.chiSquared_bijective_annotation
#check @MutualEvaluation.Replication.Example.kl_bijective_annotation

#print axioms MutualEvaluation.Binary.Rel
#print axioms MutualEvaluation.Binary.Valid
#print axioms MutualEvaluation.Binary.annotate
#print axioms MutualEvaluation.Binary.annotate_valid
#print axioms MutualEvaluation.Binary.valid_iff_annotation
#print axioms MutualEvaluation.Replication.SampleSpace
#print axioms MutualEvaluation.Replication.Transcript
#print axioms MutualEvaluation.Replication.iid
#print axioms MutualEvaluation.Replication.conditionalTranscriptLaw
#print axioms MutualEvaluation.Replication.transcriptLaw
#print axioms MutualEvaluation.Replication.firstHit
#print axioms MutualEvaluation.Replication.R_specific
#print axioms MutualEvaluation.Replication.R_null
#print axioms MutualEvaluation.Replication.annotation_clocks
#print axioms MutualEvaluation.Replication.W_chiSquared
#print axioms MutualEvaluation.Replication.H
#print axioms MutualEvaluation.Replication.W_KL
#print axioms MutualEvaluation.Replication.u_chiSquared
#print axioms MutualEvaluation.Replication.u_KL
#print axioms MutualEvaluation.Replication.pearsonScore
#print axioms MutualEvaluation.Replication.klScore
#print axioms MutualEvaluation.Replication.V_chiSquared
#print axioms MutualEvaluation.Replication.V_KL
#print axioms MutualEvaluation.Replication.r_chiSquared
#print axioms MutualEvaluation.Replication.r_KL
#print axioms MutualEvaluation.Replication.invalid_scores
#print axioms MutualEvaluation.FiniteTask.annotated
#print axioms MutualEvaluation.FiniteTask.jointMass
#print axioms MutualEvaluation.FiniteTask.reportMass
#print axioms MutualEvaluation.FiniteTask.pearson
#print axioms MutualEvaluation.FiniteTask.shannon
#print axioms MutualEvaluation.Replication.termination
#print axioms MutualEvaluation.Replication.integrable_W_chiSquared
#print axioms MutualEvaluation.Replication.integrable_W_KL
#print axioms MutualEvaluation.Replication.u_chiSquared_annotation
#print axioms MutualEvaluation.Replication.u_KL_annotation
#print axioms MutualEvaluation.Replication.u_chiSquared_collision_ratio
#print axioms MutualEvaluation.FiniteTask.posterior
#print axioms MutualEvaluation.FiniteLog.divergence
#print axioms MutualEvaluation.FiniteTask.conditionalInformation
#print axioms MutualEvaluation.Replication.V_chiSquared_eq
#print axioms MutualEvaluation.Replication.V_KL_eq
#print axioms MutualEvaluation.Replication.chiSquared_literal_optimal
#print axioms MutualEvaluation.Replication.kl_literal_optimal
#print axioms MutualEvaluation.Replication.r_chiSquared_annotation
#print axioms MutualEvaluation.Replication.r_KL_annotation
#print axioms MutualEvaluation.Replication.chiSquared_annotation_zero_iff
#print axioms MutualEvaluation.Replication.kl_annotation_zero_iff
#print axioms MutualEvaluation.Replication.chiSquared_critic_coarsening
#print axioms MutualEvaluation.Replication.kl_critic_coarsening
#print axioms MutualEvaluation.Replication.u_chiSquared_le_value
#print axioms MutualEvaluation.Replication.u_KL_le_value
#print axioms MutualEvaluation.Replication.V_chiSquared_data_processing
#print axioms MutualEvaluation.Replication.V_KL_data_processing
#print axioms MutualEvaluation.Replication.chiSquared_truthful_global_optimal
#print axioms MutualEvaluation.Replication.kl_truthful_global_optimal
#print axioms MutualEvaluation.Replication.reportingNash
#print axioms MutualEvaluation.Replication.chiSquared_truthful_nash
#print axioms MutualEvaluation.Replication.kl_truthful_nash
#print axioms MutualEvaluation.Self.fair
#print axioms MutualEvaluation.Self.Nuisance.worker
#print axioms MutualEvaluation.Self.Nuisance.literal
#print axioms MutualEvaluation.Self.Nuisance.task
#print axioms MutualEvaluation.Self.Nuisance.constant
#print axioms MutualEvaluation.Replication.Example.chiSquared_payoff_table
#print axioms MutualEvaluation.Replication.Example.kl_payoff_table
#print axioms MutualEvaluation.Replication.Example.chiSquared_regret_table
#print axioms MutualEvaluation.Replication.Example.kl_regret_table
#print axioms MutualEvaluation.Replication.Example.chiSquared_bijective_annotation
#print axioms MutualEvaluation.Replication.Example.kl_bijective_annotation
#print axioms MutualEvaluation.Replication.V_chiSquared_robust
#print axioms MutualEvaluation.Replication.V_KL_robust

/-! Type-name compatibility and unchanged tuple behavior; technical tests only. -/
section
open MutualEvaluation.Replication

example (R : Type) : Transcript R = SampleSpace R := rfl

example (R : Type) :
    SampleSpace R = (R × ((ℕ → R) × (ℕ → R))) := rfl

example {R : Type} (a : R) (s n : ℕ → R) :
    ((a, (s, n)) : SampleSpace R).1 = a := rfl

example {R : Type} (a : R) (s n : ℕ → R) :
    ((a, (s, n)) : SampleSpace R).2.1 = s := rfl

example {R : Type} (a : R) (s n : ℕ → R) :
    ((a, (s, n)) : SampleSpace R).2.2 = n := rfl

end
