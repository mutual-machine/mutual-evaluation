import Mathlib
noncomputable section -- needed for sSup
namespace MutualEvaluation

/- AUTHOR-SPAN CO-01
The kernel of a belief is an affect. A kernel affects a belief over return values. -/
abbrev Kernel (A B : Type) := A → PMF B

/- AUTHOR-SPAN CO-02
We can independently sample from two beliefs to obtain a belief over pairs. -/
def pair {A B : Type} (p : PMF A) (q : PMF B) : PMF (A × B) :=
  p.bind fun a => q.map fun b => (a, b)

/- AUTHOR-SPAN CO-03
Expected evaluation score. -/
structure Score (R Θ : Type) where
  S : Finset ℝ
  nonempty : S.Nonempty
  u : (R × R → S) → Θ → ℝ

def Score.envelope {R Θ : Type} (U : Score R Θ) (θ : Θ) : ℝ :=
  sSup (Set.range fun c => U.u c θ)

/- AUTHOR-SPAN CO-04
A joint belief is independent if it factors into its parts. -/
def independent {A B : Type} (p : PMF (A × B)) : Prop :=
  ∀ a b, p (a, b) = (p.map Prod.fst) a * (p.map Prod.snd) b

/- AUTHOR-SPAN CO-05
Binary critic primitives shared by timing and replication. -/
namespace Binary

def scores : Finset ℝ := {0, 1}
abbrev Critic (R : Type) := R × R → scores

end Binary

namespace Probability

def mass {A : Type} (p : PMF A) (a : A) : ℝ := (p a).toReal

end Probability

/- AUTHOR-SPAN CO-06
We `bind` the shared input distribution `P` through the two kernels to obtain
their joint output distribution. We independently sample once from each kernel
at the shared input and return the resulting pair of outcomes. -/
def jointLaw {X A B : Type} (P : PMF X) (left : Kernel X A) (right : Kernel X B) :
    PMF (A × B) :=
  P.bind fun x => pair (left x) (right x)

/- AUTHOR-SPAN TP-05
We `bind` the raw return through the strategy kernel to obtain the return
beliefs, i.e. what workers believe they will return. We then independently sample
twice from each belief and return an outcome. A truthful strategy returns a
point mass at the raw return. -/
def Kernel.replicate {X R : Type} (k : Kernel X R) : Kernel X (R × R) :=
  fun x => pair (k x) (k x)

@[simp]
def Kernel.truth {R : Type} : Kernel R R := PMF.pure

def truth {I R : Type} : I → Kernel R R := fun _ => Kernel.truth

/- AUTHOR-SPAN TP-06
A deviation replaces a kernel; garbling post-processes it. -/
def deviate {I X R : Type} [DecidableEq I] (σ : I → Kernel X R) (i : I) (τ : Kernel X R) :=
  Function.update σ i τ

def Kernel.garble {X R B : Type} (k : Kernel X R) (τ : Kernel R B) : Kernel X B :=
  fun x => (k x).bind τ

def garble {I X R : Type} [DecidableEq I] (σ : I → Kernel X R) (i : I) (τ : Kernel R R) :=
  deviate σ i (Kernel.garble (σ i) τ)

/- AUTHOR-SPAN CO-07
Given a state `s`, we may ask what happens if we apply a further garbling
kernel `τ`. This produces a new state `t`.
We say the value is robust under garbling if this operation weakly decreases
the value. Moreover, if the specified joint law is dependent and becomes
independent, the value must strictly decrease. -/
def robustUnderGarbling {S R A B : Type} (value : S → ℝ) (joint : S → PMF (A × B))
    (postprocess : S → Kernel R R → S) (s : S) (τ : Kernel R R) : Prop :=
  let t := postprocess s τ
  value t ≤ value s ∧
    (¬ independent (joint s) → independent (joint t) → value t < value s)

end MutualEvaluation
end