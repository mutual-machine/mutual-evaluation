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

end MutualEvaluation
end