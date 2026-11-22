import MutualEvaluation.Internal.ReplicationExamples
import MutualEvaluation.Internal.ReplicationAgreement

/-!
# Peer-free mutual evaluation through replication

Author-approved RP-01–RP-14 interface. Internal imports supply proofs;
the reviewed primitive definitions are declared only in this file.
-/

noncomputable section
open MeasureTheory
open MutualEvaluation
open MutualEvaluation.Binary MutualEvaluation.Probability
attribute [local instance] Classical.propDecidable

/-
## RP-01 — Global validity

-/

/- AUTHOR-SPAN RP-01
Literal agreement defines an equivalence relation, but a maximizing critic for VPP need not do so. Nevertheless, the distinction made between the critic rule and the evaluation scoring allows an alternative approach. It is based on a generalized agreement critic and measuring the number of same vs. different tasks until an annotation is replicated.

Fix the critic score set to $S= \{0,1 \}$ in this section. A critic rule $c:R\times R\to \{0,1\}$ can be seen as a relation. This relation is *valid* when
$$
y\sim_c y'
\quad\Longleftrightarrow\quad
c(y,y')=1
$$

defines an equivalence relation on the entire return alphabet. Notice validity is a global property, not defined by a single sample.
-/

/-
-/

namespace MutualEvaluation.Binary

def Rel {R : Type} (c : Critic R) (a b : R) : Prop := (c (a, b) : ℝ) = 1

def Valid {R : Type} (c : Critic R) : Prop := Equivalence (Rel c)

/-
**Reading note.** `Valid` is a predicate on a complete critic table. It does not
replace `Critic R` with a restricted strategy space.

## RP-02 — Finite annotation representation

-/

/- AUTHOR-SPAN RP-02
Checking validity may be difficult. However, the following result says a critic that issues finite annotations is equivalent to a valid critic.

**Theorem (finite annotation representation).** Suppose $R$ is finite. A critic is valid if and only if there are a finite annotation alphabet $B$ and a deterministic map $g:R\to B$ such that
$$
c(y,y')=c_g(y,y')
:=\mathbf 1\{g(y)=g(y')\}
\qquad\text{for every }y,y'\in R.
$$

The representation can be chosen with $|B|\le |R|$.

The key is that while the critic rule remains binary, the way in which it is used departs from VPP mechanisms. The map map $g$ associated with a valid critic is nearly implicit to the mechanism as it is not required for producing scores. Only global validity must be preserved.
-/

/-
-/

def annotate {R B : Type} (g : R → B) : Critic R := fun ab =>
  if g ab.1 = g ab.2 then ⟨1, by simp [scores]⟩ else ⟨0, by simp [scores]⟩

theorem annotate_valid {R B : Type} (g : R → B) : Valid (annotate g) := by
  apply_rules [_root_.MutualEvaluation.Binary.annotate_valid_impl]

theorem valid_iff_annotation {R : Type} [Fintype R] (c : Critic R) :
    Valid c ↔ ∃ n ≤ Fintype.card R, ∃ g : R → Fin n, c = annotate g := by
  apply_rules [_root_.MutualEvaluation.Binary.valid_iff_annotation_impl]

end MutualEvaluation.Binary

/-
**Reading note.** `Fin n` supplies the representing alphabet of size n. The
equality `c = annotate g` is equality of the entire table, including comparisons
with zero probability under a particular channel. The small proofs in the
definition merely certify that 0 and 1 belong to `scores`.

## RP-03 — The fixed-channel replication experiment

-/

/- AUTHOR-SPAN RP-03
Fix a reported worker channel $k=k_\sigma$. We will define two replication sequences using random variables based on a fixed component. First sample the fixed task $x \sim P$. Given $x$, sample a return $Y \sim k(x)$ and use this as the fixed return. The first sequence consists of alternative return replications from the fixed task. These are drawn according to
$$
\widetilde Y_n \sim k(x), \qquad n \ge 1
$$

Accordingly, the law of the sequence $(\widetilde Y_n)_{n \ge 1}$ is iid. The second sequence consists of null return replications from freshly drawn tasks sampled

$$
x_n\sim P,\quad Z_n\sim k(x_n),
\qquad n\ge1.
$$

Marginalizing out each $x_n$ the law of the sequence $(Z_n)_{n \ge 1}$ is also iid. It is obtained by sampling a task from $P$ and then appling $k.$ Conditional on the fixed task $x$, the fixed return, and replication sequences are independent. This may be represented by a product measure. It is assumed the reporting channel and critic remain fixed throughout the experiment.
-/

/-
-/

namespace MutualEvaluation.Replication
open Binary

abbrev SampleSpace (R : Type) := R × ((ℕ → R) × (ℕ → R))

abbrev Transcript (R : Type) := SampleSpace R

section Sampling
variable {X R : Type} [MeasurableSpace R]

def iid (p : PMF R) : Measure (ℕ → R) :=
  Measure.infinitePi (fun _ : ℕ => p.toMeasure)

def conditionalTranscriptLaw (P : PMF X) (k : Kernel X R) (x : X) :
    Measure (SampleSpace R) :=
  (k x).toMeasure.prod ((iid (k x)).prod (iid (P.bind k)))

def transcriptLaw [Fintype X] (P : PMF X) (k : Kernel X R) :
    Measure (SampleSpace R) :=
  ∑ x, P x • conditionalTranscriptLaw P k x

end Sampling

/-
**Reading note.** `SampleSpace R` is the infinite proof space; `Transcript R`
is retained as a definitional alias. A point t consists of the anchor `t.1`,
the specific stream `t.2.1`, and the null stream `t.2.2`.
Stream entry 0 is manuscript call 1.
Infinite streams describe potential calls, not the calls actually requested
or charged. `P.bind k` integrates out a fresh task on each null call.
`Measure.infinitePi` is the independent product law; `.prod` is the independent
product of two measures. The same k is used throughout.

These definitions formalize the sampling experiment. They do not add an
executable-loop or efficient-validity-checking claim. The probability-measure
instances and their proofs are support, not additional review items.

## RP-04 — Specific and null type-replication variables

-/

/- AUTHOR-SPAN RP-04
Given a valid critic define the alternative and null type-replication variables from the comparisons:

$$
R_{\mathrm{alternative}}
:=
\inf\{n\ge1:c(Y,\widetilde Y_n)=1\},
\qquad
R_{\mathrm{null}}
:=
\inf\{n\ge1:c(Y,Z_n)=1\},
$$

with $\inf\varnothing=\infty$. The alternative replication random variable $R_{\text{alternative}}$ is the number of same-task replications required until $\tilde Y_n$ receives the same type-annotation from the critic. Similarly, the null replication random variable $R_{\text{null}}$ counts the number of different-task replications required until $Z_n$ receives the same type-annotation.

For the analysis, choose any finite annotation representation $c=c_g$ and write

$$
A:=g(Y),\qquad
\widetilde A_n:=g(\widetilde Y_n),\qquad
A_n:=g(Z_n).
$$

Then the two replication processes can be described as the first returns for which $\widetilde A_n=A$ and $A_n=A$, respectively. The mechanism itself does not need to construct or observe the latent type-annotations.

Here are two instances of replication loop mechanisms.
-/

/-

**Reading note.** The following `firstHit` definition is part of this review.
`Nat.find h` is the least successful zero-indexed call; adding one counts calls
including the success. `ℕ∞` adds infinity, written `⊤`, for no successful call.
Its body is unchanged from the implementation; it is no longer an undisplayed
internal dependency.
-/

def firstHit (p : ℕ → Prop) : ℕ∞ :=
  if h : ∃ n, p n then ((Nat.find h + 1 : ℕ) : ℕ∞) else ⊤

def R_specific {R : Type} (c : Critic R) (t : SampleSpace R) : ℕ∞ :=
  firstHit (fun n => Binary.Rel c t.1 (t.2.1 n))

def R_null {R : Type} (c : Critic R) (t : SampleSpace R) : ℕ∞ :=
  firstHit (fun n => Binary.Rel c t.1 (t.2.2 n))

theorem annotation_clocks {R B : Type} (g : R → B) (t : SampleSpace R) :
    R_specific (annotate g) t = firstHit (fun n => g t.1 = g (t.2.1 n)) ∧
      R_null (annotate g) t = firstHit (fun n => g t.1 = g (t.2.2 n)) := by
  apply_rules [_root_.MutualEvaluation.Replication.annotation_clocks_impl]

/-
The clock functions are total even for invalid critics. The payments below
check validity before using them; defining a potential clock does not invoke
a search.

## RP-05 — Pearson collision payment

-/

/- AUTHOR-SPAN RP-05
**The Pearson collision payment.** Request one same-task return $\widetilde Y_1$. If

$$
c(Y,\widetilde Y_1)=0,
$$

stop and pay $-1$. Otherwise continue producing null replications and pay $R_{\mathrm{null}}-1$. Thus

$$
W_{\chi^2}
=
\begin{cases}
-1,
&c(Y,\widetilde Y_1)=0,\\
R_{\mathrm{null}}-1,
&c(Y,\widetilde Y_1)=1.
\end{cases}
$$

The marginal search is not run after a mismatch.
-/

/-

**Accepted notation correspondence:** $K_{\mathrm{marg}}=R_{\mathrm{null}}$
and $K_{\mathrm{same}}=R_{\mathrm{specific}}$. No additional clocks are defined.
-/

def W_chiSquared {R : Type} (c : Critic R) (t : SampleSpace R) : ℝ :=
  if Valid c then
    if Binary.Rel c t.1 (t.2.1 0) then
      if R_null c t = ⊤ then 0 else (R_null c t).toNat - 1
    else -1
  else 0

/-
**Reading note.** The inner comparison tests score 1. Since scores are binary,
its other branch is the authored score-0 mismatch. That branch is −1 regardless
of the null stream. The zero extension is used only if the invoked null search
does not terminate. In the finite branch, `toNat` recovers the number of calls;
the subtraction here is real subtraction.

## RP-06 — Harmonic two-clock payment

-/

/- AUTHOR-SPAN RP-06
**The KL two-clock payment.** Run both replications. With
$$
H_0:=0,
\qquad
H_m:=\sum_{j=1}^{m}\frac1j,
$$

pay

$$
W_{\mathrm{KL}}
:=
H_{R_{\mathrm{null}}-1}
-
H_{R_{\mathrm{alternative}}-1}.
$$

These are random scoring procedures, not the critic rule itself. When a score is viewed as a random variable, extend it by zero on nonterminating paths; the theorem below shows that those paths are null.

Each mechansim can be defined from the specific and null replication variables. Neither requires return probabilities, likelihood ratios, reports, or direct observation of the latent task or type-annotations. 
-/

/-
-/

def H (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, ((j : ℝ) + 1)⁻¹

def W_KL {R : Type} (c : Critic R) (t : SampleSpace R) : ℝ :=
  if Valid c then
    if R_null c t = ⊤ ∨ R_specific c t = ⊤ then 0
    else H ((R_null c t).toNat - 1) - H ((R_specific c t).toNat - 1)
  else 0

/-
**Reading note.** `Finset.range n` indexes 0 through n−1, so H sums the
reciprocals of 1 through n and gives zero at n = 0. The arguments to H count
failures before success. The payment is zero for an invalid critic or when
either invoked search fails to terminate.

As acknowledged in the earlier decision, reports enter through comparisons.
This request does not include a separate computational-access or
noninterference theorem.

## RP-07 — Channel-level evaluation scores, envelopes, and regret

-/

/- AUTHOR-SPAN RP-07
**Channel-level evaluation scores.** The parameter of the replication loop score is the channel instance $(P,k)$. Let
$$
u_{\chi^2}(c;P,k)
\qquad\text{and}\qquad
u_{\mathrm{KL}}(c;P,k)
$$

denote the corresponding expected payments, with score zero for invalid critics. This separates the critic rule, random payment, and evaluation score as distinct constructs:

$$
c
\quad\longmapsto\quad
W_\bullet(c;P,k)
\quad\longmapsto\quad
u_\bullet(c;P,k)
=
\mathbb E[W_\bullet(c;P,k)].
$$

The envelope and critic regret are then the generic score quantities

$$
V_\bullet(P,k):=\sup_c u_\bullet(c;P,k),
\qquad
r_\bullet(c;P,k):=
V_\bullet(P,k)-u_\bullet(c;P,k).
$$
-/

/-
-/

section Scores
variable {X R : Type} [MeasurableSpace R]

def u_chiSquared [Fintype X] (c : Critic R) (P : PMF X) (k : Kernel X R) : ℝ :=
  ∫ t, W_chiSquared c t ∂transcriptLaw P k

def u_KL [Fintype X] (c : Critic R) (P : PMF X) (k : Kernel X R) : ℝ :=
  ∫ t, W_KL c t ∂transcriptLaw P k

def pearsonScore [Fintype X] : Score R (PMF X × Kernel X R) where
  S := scores
  nonempty := by classical simp [scores]
  u := fun c θ => u_chiSquared c θ.1 θ.2

def klScore [Fintype X] : Score R (PMF X × Kernel X R) where
  S := scores
  nonempty := by classical simp [scores]
  u := fun c θ => u_KL c θ.1 θ.2

def V_chiSquared [Fintype X] (P : PMF X) (k : Kernel X R) : ℝ :=
  (pearsonScore (X := X) (R := R)).envelope (P, k)

def V_KL [Fintype X] (P : PMF X) (k : Kernel X R) : ℝ :=
  (klScore (X := X) (R := R)).envelope (P, k)

def r_chiSquared [Fintype X] (c : Critic R) (P : PMF X) (k : Kernel X R) : ℝ :=
  V_chiSquared P k - u_chiSquared c P k

def r_KL [Fintype X] (c : Critic R) (P : PMF X) (k : Kernel X R) : ℝ :=
  V_KL P k - u_KL c P k

theorem invalid_scores [Fintype X] (c : Critic R) (hc : ¬ Valid c)
    (P : PMF X) (k : Kernel X R) :
    u_chiSquared c P k = 0 ∧ u_KL c P k = 0 := by
  apply_rules [_root_.MutualEvaluation.Replication.invalid_scores_impl]

end Scores
end MutualEvaluation.Replication

/-
**Reading note.** These remain the original Bochner integrals, not definitions
by information targets. Their envelopes include every binary critic.
Integrability is proved in RP-09 rather than inferred from the total integral
operation. KL stays channel-parameterized; TwoPairOutcome's four-report law is not assumed
to determine its score.

## RP-08 — Information conventions

-/

/- AUTHOR-SPAN RP-08
**Information conventions.** Write $p_Z$ and $p_{X,Z}$ for the marginal and joint distributions of a finite-valued variable $Z$ and the task. The term $\log$ refers to the natural logarithm. Now define
$$
I_{\chi^2}(X;Z)
:=
\sum_{x,z}
\frac{p_{X,Z}(x,z)^2}{P(x)p_Z(z)}
-1,
$$

and

$$
I(X;Z)
:=
\sum_{x,z}
p_{X,Z}(x,z)
\log
\frac{p_{X,Z}(x,z)}
     {P(x)p_Z(z)}.
$$

Terms with zero denominator are omitted, and zero-mass logarithmic terms contribute zero.
-/

/-
-/

namespace MutualEvaluation.FiniteTask
open Probability
variable {X R B : Type}

def annotated (k : Kernel X R) (g : R → B) : Kernel X B :=
  fun x => (k x).map g

variable (P : PMF X) (k : Kernel X R)

def jointMass (x : X) (a : R) : ℝ :=
  mass P x * mass (k x) a

def reportMass (a : R) : ℝ :=
  mass (P.bind k) a

def pearson [Fintype X] [Fintype R] : ℝ :=
  (∑ x, ∑ a, (jointMass P k x a)^2 /
    (mass P x * reportMass P k a)) - 1

def shannon [Fintype X] [Fintype R] : ℝ :=
  ∑ x, ∑ a, jointMass P k x a *
    Real.log (jointMass P k x a / (mass P x * reportMass P k a))

end MutualEvaluation.FiniteTask

/-
**Reading note.** `annotated k g` is the channel of annotation labels, used
for analysis rather than as an additional worker strategy. Lean's real division
by zero contributes zero. Proof support establishes that a null product-reference
atom has null joint mass, so these conventions do not discard positive joint
mass or hide singular information terms.

## RP-09 — Termination, integrability, and unbiasedness

-/

/- AUTHOR-SPAN RP-09
The replication loop mechanisms both terminate and equal their corresponding mutual information functional. Specifically, the replication procedure evaluates the information *retained* by the equivalence classes of the critic. 

**Theorem (termination, integrability, and unbiasedness).** For finite $X,R$, every fixed channel $k$, and every valid critic $c$, each invoked replication sequence almost surely and both payments are integrable. If $c=c_g$ and $A=g(Y)$, then
$$
\begin{aligned}
u_{\chi^2}(c;P,k)
&=
\sum_{a:p_A(a)>0}
\frac{\Pr(A=a,A'=a)}{p_A(a)}
-1 = I_{\chi^2}(X;A),
\\[1ex]
u_{\mathrm{KL}}(c;P,k)
&=
I(X;A),
\end{aligned}
$$

where $A'=g(\widetilde Y_1)$. Here $A$ and $A'$ are annotations of alternative replications, not annotations of null replications.
-/

/-
-/

namespace MutualEvaluation.Replication
open Binary Probability FiniteTask

section Termination
variable {X R : Type} [MeasurableSpace R] [Fintype R]
  [MeasurableSingletonClass R]

theorem termination [Fintype X] (c : Critic R) (hc : Valid c)
    (P : PMF X) (k : Kernel X R) :
    ∀ᵐ t ∂transcriptLaw P k, R_specific c t ≠ ⊤ ∧ R_null c t ≠ ⊤ := by
  apply_rules [_root_.MutualEvaluation.Replication.termination_impl]

end Termination

section Integrability
variable {R : Type} [MeasurableSpace R] [Fintype R]
  [MeasurableSingletonClass R]
variable {X : Type}

theorem integrable_W_chiSquared [Fintype X] (c : Critic R)
    (P : PMF X) (k : Kernel X R) :
    Integrable (W_chiSquared c) (transcriptLaw P k) := by
  apply_rules [_root_.MutualEvaluation.Replication.integrable_W_chiSquared_impl]

theorem integrable_W_KL [Fintype X] (c : Critic R)
    (P : PMF X) (k : Kernel X R) :
    Integrable (W_KL c) (transcriptLaw P k) := by
  apply_rules [_root_.MutualEvaluation.Replication.integrable_W_KL_impl]

end Integrability

section Unbiasedness
variable {X R B : Type} [Fintype X] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R] [Fintype B]

theorem u_chiSquared_annotation (P : PMF X) (k : Kernel X R) (g : R → B) :
    u_chiSquared (annotate g) P k = pearson P (annotated k g) := by
  apply_rules [_root_.MutualEvaluation.Replication.u_chiSquared_annotation_impl]

theorem u_KL_annotation (P : PMF X) (k : Kernel X R) (g : R → B) :
    u_KL (annotate g) P k = shannon P (annotated k g) := by
  apply_rules [_root_.MutualEvaluation.Replication.u_KL_annotation_impl]

end Unbiasedness

section Collision
variable {X R : Type} [Fintype X] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]

theorem u_chiSquared_collision_ratio {B : Type} [Fintype B]
    (P : PMF X) (k : Kernel X R) (g : R → B) :
    u_chiSquared (annotate g) P k =
      (∑ b, mass (P.bind fun x =>
          pair (annotated k g x) (annotated k g x)) (b, b) /
        reportMass P (annotated k g) b) - 1 := by
  apply_rules [_root_.MutualEvaluation.Replication.u_chiSquared_collision_ratio_impl]

end Collision
end MutualEvaluation.Replication

/-
**Reading note.** Termination makes both potential clocks finite almost surely,
and hence every invoked search finite. Integrability also covers invalid
critics because their payments are zero. The expectation identities are proved
from the actual independent streams, not an assumed count law or an unbiasedness
hypothesis. Null tasks and anchors are handled by the sampling law.

The pair in the collision formula is sampled independently conditional on one
task. Its null-denominator terms contribute zero. No measurable-space structure
on B is required. The two Pearson equalities above give the entire displayed
collision-ratio/information chain.

## RP-10 — Posteriors and conditional information

-/

/- AUTHOR-SPAN RP-10
**Envelope and posterior regret.** On the support of reports and annotations define the conditional proability of a report given the critic type-annotation.
$$
\pi_y(x):=\Pr(X=x\mid Y=y),
\qquad
\bar\pi_a(x):=\Pr(X=x\mid A=a).
$$

Since $A=g(Y)$ we have an alternative representation in terms of conditional mutual information.

$$
I(X;Y\mid A)
:=
\sum_{y:p_Y(y)>0}
p_Y(y)
\sum_x
\pi_y(x)
\log
\frac{\pi_y(x)}
     {\bar\pi_{g(y)}(x)}.
$$

Note zero-mass terms contribute zero.
-/

/-
-/

namespace MutualEvaluation.FiniteTask
variable {X R : Type} (P : PMF X) (k : Kernel X R)

def posterior (a : R) (x : X) : ℝ :=
  jointMass P k x a / reportMass P k a

end MutualEvaluation.FiniteTask

namespace MutualEvaluation.FiniteLog
variable {A : Type} [Fintype A]

def divergence (p q : A → ℝ) : ℝ :=
  ∑ a, p a * Real.log (p a / q a)

end MutualEvaluation.FiniteLog

namespace MutualEvaluation.FiniteTask
variable {X R B : Type} (P : PMF X) (k : Kernel X R)

def conditionalInformation [Fintype X] [Fintype R] (g : R → B) : ℝ :=
  ∑ a, reportMass P k a *
    FiniteLog.divergence (posterior P k a) (posterior P (annotated k g) (g a))

end MutualEvaluation.FiniteTask

/-
**Reading note.** The posterior is extended by zero at a null report.
`divergence` is explicitly the finite logarithmic sum, not a claim about
arbitrary singular probability vectors. In its use here, proof support
establishes domination of each report posterior by its class posterior.
Thus the displayed conditional-information sum has no hidden singular terms.
All logarithms are natural.

## RP-11 — Envelopes, posterior regret, and sufficiency

-/

/- AUTHOR-SPAN RP-11
There are simple expressions for the game valuation and critic regret. 

**Theorem (envelopes, regret, and sufficiency).** Maximizing over the full binary critic space gives

$$
V_{\chi^2}(P,k)
=
I_{\chi^2}(X;Y),
\qquad
V_{\mathrm{KL}}(P,k)
=
I(X;Y).
$$

Both envelopes are attained by the literal-agreement critic

$$
c_{\mathrm{id}}(y,y')
:=
\mathbf1\{y=y'\}.
$$

For every valid critic $c=c_g$, with $A=g(Y)$,

$$
\begin{aligned}
r_{\chi^2}(c;P,k)
&=
I_{\chi^2}(X;Y)
-
I_{\chi^2}(X;A)
\\
&=
\sum_{y:p_Y(y)>0}
p_Y(y)
\sum_{x:P(x)>0}
\frac{
  \bigl(\pi_y(x)-\bar\pi_{g(y)}(x)\bigr)^2
}{
  P(x)
},
\\[1ex]
r_{\mathrm{KL}}(c;P,k)
&=
I(X;Y)-I(X;A)
\\
&=
I(X;Y\mid A).
\end{aligned}
$$

One useful corollary is that for either score, a valid critic has zero regret exactly when

$$
\pi_y=\bar\pi_{g(y)}
\qquad
\text{for every }y\text{ with }p_Y(y)>0.
$$

This leaves an optimal critic free to merge reports that leave beliefs unchanged over tasks. This separates type-annotation from information loss. Literal agreement always attains the envelope. However, this need not be the only optimal critic. This is useful since the runtime may depend on the complexity of the type-annotations.
-/

/-
-/

namespace MutualEvaluation.Replication
open Binary Probability FiniteTask

section Consequences
variable {X R : Type} [Fintype X] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
variable (P : PMF X) (k : Kernel X R)

theorem V_chiSquared_eq : V_chiSquared P k = pearson P k := by
  apply_rules [_root_.MutualEvaluation.Replication.V_chiSquared_eq_impl]

theorem V_KL_eq : V_KL P k = shannon P k := by
  apply_rules [_root_.MutualEvaluation.Replication.V_KL_eq_impl]

theorem chiSquared_literal_optimal :
    u_chiSquared (annotate id) P k = V_chiSquared P k := by
  apply_rules [_root_.MutualEvaluation.Replication.chiSquared_literal_optimal_impl]

theorem kl_literal_optimal :
    u_KL (annotate id) P k = V_KL P k := by
  apply_rules [_root_.MutualEvaluation.Replication.kl_literal_optimal_impl]

theorem r_chiSquared_annotation {B : Type} [Fintype B] (g : R → B) :
    r_chiSquared (annotate g) P k =
      ∑ x, (∑ a, reportMass P k a *
        (posterior P k a x - posterior P (annotated k g) (g a) x)^2) /
          mass P x := by
  apply_rules [_root_.MutualEvaluation.Replication.r_chiSquared_annotation_impl]

theorem r_KL_annotation {B : Type} [Fintype B] (g : R → B) :
    r_KL (annotate g) P k = conditionalInformation P k g := by
  apply_rules [_root_.MutualEvaluation.Replication.r_KL_annotation_impl]

theorem chiSquared_annotation_zero_iff {B : Type} [Fintype B] (g : R → B) :
    r_chiSquared (annotate g) P k = 0 ↔
      ∀ a, 0 < reportMass P k a →
        posterior P k a = posterior P (annotated k g) (g a) := by
  apply_rules [_root_.MutualEvaluation.Replication.chiSquared_annotation_zero_iff_impl]

theorem kl_annotation_zero_iff {B : Type} [Fintype B] (g : R → B) :
    r_KL (annotate g) P k = 0 ↔
      ∀ a, 0 < reportMass P k a →
        posterior P k a = posterior P (annotated k g) (g a) := by
  apply_rules [_root_.MutualEvaluation.Replication.kl_annotation_zero_iff_impl]

/-
**Reading note.** The information-difference equalities follow by substituting
RP-09 and the displayed envelope equalities into RP-07's regret definitions.
The Pearson finite sums are written task-first; exchanging the finite sums
gives the manuscript's report-first expression. Null prior coordinates
contribute zero. By RP-02, statements for `annotate g` cover every valid critic.
Sufficiency concerns positive-mass reports, not global validity or full support.

## RP-12 — Critic garbling and joint payoff maximality

-/

/- AUTHOR-SPAN RP-12
**Critic garbling and truthful equilibrium.** Type-annotation gives a second garbling operation. If $c=c_g$ is valid and $h:B\to C$, then
$$
c_{h\circ g}(y,y')
=
\mathbf1\{h(g(y))=h(g(y'))\}
$$

is another valid critic obtained by garbling the annotation classes. For either score,

$$
u_\bullet(c_{h\circ g};P,k)
\le
u_\bullet(c_g;P,k).
$$

Indeed, for every garbling kernel $\sigma_0$ and every critic $d$,

$$
u_\bullet(d;P,k_\sigma)
\le
V_\bullet(P,k_\sigma)
\le
V_\bullet(P,w_0).
$$

If $c_*$ is any critic optimal at truth, then

$$
V_\bullet(P,w_0)
=
u_\bullet(c_*;P,w_0)
=
I_\bullet(X;Y_0),
$$

where

$$
x\sim P,
\qquad
Y_0\sim w_0(x),
$$

and $I_\bullet$ denotes $I_{\chi^2}$ or $I$, respectively. Therefore

$$
u_\bullet(d;P,k_\sigma)
\le
u_\bullet(c_*;P,w_0).
$$
-/

/-
-/

theorem chiSquared_critic_coarsening {B C : Type} [Fintype B] [Fintype C]
    (g : R → B) (h : B → C) :
    u_chiSquared (annotate (h ∘ g)) P k ≤ u_chiSquared (annotate g) P k := by
  apply_rules [_root_.MutualEvaluation.Replication.chiSquared_critic_coarsening_impl]

theorem kl_critic_coarsening {B C : Type} [Fintype B] [Fintype C]
    (g : R → B) (h : B → C) :
    u_KL (annotate (h ∘ g)) P k ≤ u_KL (annotate g) P k := by
  apply_rules [_root_.MutualEvaluation.Replication.kl_critic_coarsening_impl]

theorem u_chiSquared_le_value (c : Critic R) :
    u_chiSquared c P k ≤ V_chiSquared P k := by
  apply_rules [_root_.MutualEvaluation.Replication.u_chiSquared_le_value_impl]

theorem u_KL_le_value (c : Critic R) :
    u_KL c P k ≤ V_KL P k := by
  apply_rules [_root_.MutualEvaluation.Replication.u_KL_le_value_impl]

theorem V_chiSquared_data_processing {B : Type} [Fintype B]
    [MeasurableSpace B] [MeasurableSingletonClass B] (τ : Kernel R B) :
    V_chiSquared P (fun x => (k x).bind τ) ≤ V_chiSquared P k := by
  apply_rules [_root_.MutualEvaluation.Replication.V_chiSquared_data_processing_impl]

theorem V_KL_data_processing {B : Type} [Fintype B]
    [MeasurableSpace B] [MeasurableSingletonClass B] (τ : Kernel R B) :
    V_KL P (fun x => (k x).bind τ) ≤ V_KL P k := by
  apply_rules [_root_.MutualEvaluation.Replication.V_KL_data_processing_impl]

theorem chiSquared_truthful_global_optimal (c : Critic R)
    (hc : u_chiSquared c P k = V_chiSquared P k)
    (d : Critic R) (σ : Kernel R R) :
    u_chiSquared d P (fun x => (k x).bind σ) ≤ u_chiSquared c P k := by
  apply_rules [_root_.MutualEvaluation.Replication.chiSquared_truthful_global_optimal_impl]

theorem kl_truthful_global_optimal (c : Critic R)
    (hc : u_KL c P k = V_KL P k)
    (d : Critic R) (σ : Kernel R R) :
    u_KL d P (fun x => (k x).bind σ) ≤ u_KL c P k := by
  apply_rules [_root_.MutualEvaluation.Replication.kl_truthful_global_optimal_impl]

end Consequences
end MutualEvaluation.Replication

/-
**Reading note.** RP-02 proves that coarsening still gives a valid critic.
For truthful maximality, k is the raw channel and σ is any fixed reporting
kernel. The bounds permit changing both critic and reporting kernel; c is
required only to be optimal at the ungarbled channel.

## RP-13 — Truthful single-worker equilibrium

-/

/- AUTHOR-SPAN RP-13
**Corollary (truthful equilibrium under replication).** Truth and any critic optimal at truth jointly maximize the common evaluation score and form a Nash equilibrium of the corresponding replication game. Worker deviations choose one reporting kernel before the replication experiment begins.
-/

/-
-/

namespace MutualEvaluation.Replication
open Binary

def reportingNash {X R : Type} (U : Score R (PMF X × Kernel X R))
    (P : PMF X) (w : Kernel X R) (σ : Kernel R R)
    (c : R × R → U.S) : Prop :=
  (∀ d, U.u d (P, fun x => (w x).bind σ) ≤
    U.u c (P, fun x => (w x).bind σ)) ∧
  ∀ τ : Kernel R R, U.u c (P, fun x => (w x).bind τ) ≤
    U.u c (P, fun x => (w x).bind σ)

variable {X R : Type} [Fintype X] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
variable (P : PMF X) (w : Kernel X R)

theorem chiSquared_truthful_nash (c : Critic R)
    (hc : u_chiSquared c P w = V_chiSquared P w) :
    reportingNash (pearsonScore (X := X) (R := R)) P w PMF.pure c := by
  apply_rules [_root_.MutualEvaluation.Replication.chiSquared_truthful_nash_impl]

theorem kl_truthful_nash (c : Critic R)
    (hc : u_KL c P w = V_KL P w) :
    reportingNash (klScore (X := X) (R := R)) P w PMF.pure c := by
  apply_rules [_root_.MutualEvaluation.Replication.kl_truthful_nash_impl]

end MutualEvaluation.Replication

/-
**Reading note.** `reportingNash` spells out the two common-payoff best-response
inequalities for one worker and one critic. `PMF.pure` is truthful reporting.
This is not TwoPairOutcome's two-worker `nash` predicate or a TwoPairOutcome robustness certificate.
Deviations replace the whole reporting kernel before sampling; adaptive
within-loop strategies are outside this interface.

## RP-14 — Nuisance removal, constant annotation, and relabeling

-/

/- AUTHOR-SPAN RP-14
**Examples.** Let $X$ and $U$ be independent fair bits and let the truthful return be

$$
Y_0=(X,U).
$$

Literal agreement retains the full report. The nuisance-removing annotation

$$
g(x,u)=x
$$

strictly compresses the return alphabet but retains all task information. Both critics therefore attain Pearson information $1$ and Shannon information $\log 2$, and both have zero regret.

A constant annotation retains no task information, giving regrets $1$ and $\log2$, respectively. Any bijective annotation merely relabels reports and again has zero regret.

These examples illustrates the following three notions are distinct: the size of the annotation alphabet, the amount of task information retained by the critic, and the sampling cost of implementing its evaluation score. The next section studies the last of these.
-/

/-
-/

namespace MutualEvaluation.Self

def fair : PMF Bool := PMF.uniformOfFintype Bool

end MutualEvaluation.Self

namespace MutualEvaluation.Self.Nuisance
open Binary

def worker : Kernel Bool (Bool × Bool) := fun x => fair.map fun u => (x, u)

def literal : Critic (Bool × Bool) := annotate id

def task : Critic (Bool × Bool) := annotate Prod.fst

def constant : Critic (Bool × Bool) := annotate (fun _ => ())

end MutualEvaluation.Self.Nuisance

namespace MutualEvaluation.Replication.Example
open Binary
open _root_.MutualEvaluation.Self (fair)
open _root_.MutualEvaluation.Self.Nuisance (worker literal task constant)

variable [MeasurableSpace (Bool × Bool)]
  [MeasurableSingletonClass (Bool × Bool)]

theorem chiSquared_payoff_table :
    u_chiSquared literal fair worker = 1 ∧
      u_chiSquared task fair worker = 1 ∧
      u_chiSquared constant fair worker = 0 := by
  apply_rules [_root_.MutualEvaluation.Replication.Example.chiSquared_payoff_table_impl]

theorem kl_payoff_table :
    u_KL literal fair worker = Real.log 2 ∧
      u_KL task fair worker = Real.log 2 ∧
      u_KL constant fair worker = 0 := by
  apply_rules [_root_.MutualEvaluation.Replication.Example.kl_payoff_table_impl]

theorem chiSquared_regret_table :
    r_chiSquared literal fair worker = 0 ∧
      r_chiSquared task fair worker = 0 ∧
      r_chiSquared constant fair worker = 1 := by
  apply_rules [_root_.MutualEvaluation.Replication.Example.chiSquared_regret_table_impl]

theorem kl_regret_table :
    r_KL literal fair worker = 0 ∧
      r_KL task fair worker = 0 ∧
      r_KL constant fair worker = Real.log 2 := by
  apply_rules [_root_.MutualEvaluation.Replication.Example.kl_regret_table_impl]

theorem chiSquared_bijective_annotation {B : Type} [Fintype B]
    (g : Bool × Bool → B) (hg : Function.Bijective g) :
    u_chiSquared (annotate g) fair worker = 1 ∧
      r_chiSquared (annotate g) fair worker = 0 := by
  apply_rules [_root_.MutualEvaluation.Replication.Example.chiSquared_bijective_annotation_impl]

theorem kl_bijective_annotation {B : Type} [Fintype B]
    (g : Bool × Bool → B) (hg : Function.Bijective g) :
    u_KL (annotate g) fair worker = Real.log 2 ∧
      r_KL (annotate g) fair worker = 0 := by
  apply_rules [_root_.MutualEvaluation.Replication.Example.kl_bijective_annotation_impl]

end MutualEvaluation.Replication.Example
end

namespace MutualEvaluation.Replication

section
variable {X R : Type} [Fintype X] [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]

theorem V_chiSquared_robust (P : PMF X) (k : Kernel X R) (τ : Kernel R R) :
    robustUnderGarbling (V_chiSquared P) (jointLaw P Kernel.truth) Kernel.garble k τ :=
  V_chiSquared_robust_impl P k τ

theorem V_KL_robust (P : PMF X) (k : Kernel X R) (τ : Kernel R R) :
    robustUnderGarbling (V_KL P) (jointLaw P Kernel.truth) Kernel.garble k τ :=
  V_KL_robust_impl P k τ

end
end MutualEvaluation.Replication

