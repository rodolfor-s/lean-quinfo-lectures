/-
Initial file to showcase Lean to students.

Initial thoughts: I should write about the Lean viewport in VSCode, basic
environments, tactics, types (e.g. in contrast to sets).
-/

-- see https://github.com/leanprover/verso-slides#slide-metadata for slide
-- metadata fields

import Mathlib.Tactic
-- import Mathlib.Topology.Basic
import VersoSlides
import Verso.Doc.Concrete

open VersoSlides

#doc (Slides) "Lecture 1: Introduction" =>

# `L∃∀N`-verified Quantum Information Theory

- *RRS* to QIC891, Fall 2026
- Lecture 1, 2026-09-15

## {attr (style := "font-size: 4em;")}[$`\Gamma ⊢ t : T`]

:::notes
Speaker notes
:::

# Lecture logistics

%%%
vertical := some true
%%%

- Some change of rooms. Space Room from today (15th) to September 22
- 24th in Sky, 29th in Time, and 1st of October in Sky again
- A repository with these slides and Lean code will be made public
- PSI Room Office hours

## Learning outcomes

- Create a Lean project repository from scratch
- Understand math in a Lean way
- Be able to assess the quality of AI-written code

## Assignment: one project at the end

- Overarching Goal: Make a contributing Pull Request to the Github repository of Physlib, Quantumlib, Lean-QuantumInfo, or Mathlib.
    - Meaning: your work is also an actual citable contribution!
    - (Of course, it will not be judged by whether the PR was accepted)
- I'm compiling and should have a list of suggestions in the webpage available
soon
    - This includes non-QI options
    - Projects that are not exactly formalization are also welcome. Maybe you
    want to build your own kernel? _Let's teach each other!_

:::notes
Housekeeping (title, logistics, outcomes, assignment): ~10 min
Types vs. sets + live REPL demo: ~10 min
Maths-as-code / propositions-as-types: ~8 min
Theorem-proving demo: ~8 min
Quantumlib/Physlib: ~3 min
Kernel trust + LKA arena: ~10 min
Kernel soundness/completeness + LKA tutorial: ~8 min
Two postmortems (dense quotes, embedded blog iframes): ~20 min
AI/autoformalization section (FLT ×2, Navier-Stokes): ~12 min
:::

# Maths under a different guise

%%%
vertical := some true
%%%

1. Set theory and the Zermelo--Frankel axioms, with the axiom of choice
2. *Type theory*

What kind of differences do we expect to find? Is $`\mathbb{R}` a *set* or a *type*, in Lean?

```lean
variable {x : ℝ}
#check x -- as declared above, x is of type ℝ

/- type judgment is defined to output the RHS -/
#check (x : ℝ)

#check (Set ℝ)
-- the set built from type ℝ is another data term in Type
```

# Maths as *code*

```code lean
import Mathlib.Tactic
-- import Mathlib.Topology.Basic

import VersoSlides
import Verso.Doc.Concrete

open VersoSlides
/- Preamble of this exact slide you're reading -/
```

- Are these two things different after all?

## _Propositions as Types_ paradigm

:::notes
This is also a question of how we do or research mathematics (and hence,
theoretical physics).
.
An anecdote: I tried to compile the Lean source code that
produces these slides, but a variable I tried to declare was
already defined *in one of the slides*; the compilation returned
the error "variable already defined"!
:::

:::notes
Mention Mathematica, Sympy.
How is Lean different?
:::

# Theorem-proving code

```lean
-- Check definition of a topological space in mathlib
#check TopologicalSpace

-- Check that √2 is irrational
#check irrational_sqrt_two

-- Verify a simple identity using the ring tactic
example (a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring

-- Or a numeric check
#reduce (2 : ℕ) + 2 -- should print 4

/- from PatrickMossat/GlimpseOfLean -/
def continuous_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

#check continuous_at
```

# Quantumlib and Physlib more broadly

Coding, mathematics, and possibly theoretical physics without *context-switching*
- [`leanprover-community/physlib`](https://github.com/leanprover-community/physlib)
- [`Timeroot/Lean-QuantumInfo`](https://github.com/Timeroot/Lean-QuantumInfo)

# In what do we _trust?_

%%%
vertical := some true
%%%

- The main source of trust: the Lean _*KERNEL*_
    - It's a [folder on Github](https://github.com/leanprover/lean4/tree/master/src/kernel) for all to see.
- The "flow of trust". What else should we rely on?
    - Lean elaborator: what you're writing is being translated honestly to the kernel
    - Hardware
    - Possibly, the Lean compiler
    - Possibly, external type-checkers
- The Lean Kernel Arena (LKA) 🏟️
    - `def`: Ongoing adversarial multi-implementation conformance
    suite.

[`Lean@leanprover` announcement on Twitter of the LKA](https://x.com/leanprover/status/2087946457890578602)
> The diversity is the point. A bug that lets one kernel accept an
invalid proof would have to exist in every kernel at once to go
undetected.

## {attr (style := "font-size: 1.6em")}[🏟️]

[arena.lean-lang.org](https://arena.lean-lang.org/)
```html
<iframe src="https://arena.lean-lang.org/" width="100%" class="r-stretch" style="border:0;"></iframe>
```

# The Lean Kernel

%%%
vertical := some true
%%%

- Soundness
    - `def`: a kernel is sound iff it never accepts a proof term of
    False. By _ex falso_, proving `False`
    implies anything can be proven. *Catastrophic* ⚠️
    - Accepting an incorrect proof.
- Completeness
    - `def`: Rejecting a correct proof.

## LKA Tutorial Test Cases

[List of test cases](https://arena.lean-lang.org/tutorial/)
```html
<div class="r-stretch" style="width: 80%; height: 100%; margin: 0 auto; overflow: auto;">
<iframe src="https://arena.lean-lang.org/tutorial/"
style="border: 0;
        width: 80%;
        height: 100%;
        zoom: 2;
        <!-- w:100,zoom:1.5 for full page width -->
        <!-- w:80,zoom:2 for hidden left-hand sidebar -->
        "></iframe>
</div>
```

:::notes
Wrongly-accepted invalid proofs : FALSE POSITIVE : UN-SOUNDNESS
Wrongly-rejected valid proofs : FALSE NEGATIVE : inCOMPLETENESS
- https://github.com/leanprover/lean-kernel-arena/tree/master/tutorial#tutorial-test-cases
- (CLAUDE) Priority order: first by wrongly-accepted invalid
proofs, then by wrongly-rejected valid proofs, then by time on the
mathlib test, then by number of declined tests ---
i.e. soundness first, completeness second, speed third
:::

# What if the Lean Kernel has bugs?

%%%
vertical := some true
%%%

- The landscape is rapidly changing. A fully trusted kernel, and
thus a fully trusted Lean should pass an _audit_.
- First bugs have been reported as early as _a month ago!_
- Two _Postmortem_.

Wikipedia definition:
> Post-mortem is debugging of the program after it has already crashed.

## Postmortem, 2026-08-01

[Kernel Soundness Bug #14576](https://leodemoura.github.io/blog/2026-8-1-postmortem-for-kernel-soundness-bug-14576/)

::::::attr (class := "r-stretch")
:::::hstack
```html
<div style="flex: 1; width: 100%; height: 100%; overflow: auto;">
<iframe src="https://leodemoura.github.io/blog/2026-8-1-postmortem-for-kernel-soundness-bug-14576/"
style="border: 0;
        width: 100%;
        height: 100%;
        zoom: 2;
        "></iframe>
</div>
```
:::attr (style := "flex: 1")
- `nanoda` external checker in Rust
- `lean4lean` external checker in Lean
:::
:::::
::::::

:::notes
- The bug (quote): "when the kernel eliminates a nested occurrence under
  an inductive type `T` with parameters `Ds`, and these parameters are
  phantom (not mentioned in constructor fields), they disappear" —
  i.e. ill-typed arguments slip through, undetected.
- How it was found (quote): "On July 25, Ramana Kumar published a
  repository containing a `sorry`-free 'disproof' of the Collatz
  conjecture, produced with AI assistance."
- Wikipedia, Collatz conjecture: iterate n → n/2 if even, 3n+1 if odd;
  conjecture says every positive integer eventually reaches 1 —
  verified up to 2.36×10^21, but no general proof exists.
- Fast turnaround (quote): "On July 28, Kiran Gopinathan reduced it to
  a small proof of `False`... We pushed a fix one hour after the report."
- Root cause (quote): "This is an implementation bug, not a hole in
  Lean's meta-theory."
- Why the frontend didn't catch it (quote): "The bug is only reachable
  through metaprogramming, by sending the inductive declaration to the
  kernel directly. The frontend checks the arguments and catches the
  ill-typed term."
- The lesson (quote): "The kernel has to reject ill-typed declarations
  on its own, in its own process." — trust the kernel, not the frontend.
:::

## Postmortem, 2026-08-24

[Kernel Soundness Bug Hunt](https://leodemoura.github.io/blog/2026-8-24-postmortem-for-the-kernel-soundness-bug-hunt/)

::::::attr (class := "r-stretch")
:::::hstack
```html
<div style="flex: 1; width: 100%; height: 100%; overflow: auto;">
<iframe src="https://leodemoura.github.io/blog/2026-8-24-postmortem-for-the-kernel-soundness-bug-hunt/"
style="border: 0;
        width: 100%;
        height: 100%;
        zoom: 2;
        "></iframe>
</div>
```
:::attr (style := "flex: 1")
- `lake check --paranoid`
    - `lean4checker`
- `lean-inductive-models`
    - “Lean's theory of inductive types is well understood”
:::
:::::
::::::

:::notes
- Setup (quote): "Daniel used OpenAI internal models to discover new
  soundness issues in the official Lean kernel and runtime." (following
  #14576, a ~3-week hunt, July 30 – August 20.)
- Why bother (quote): "We consider AI-generated proofs a potential
  source of malicious proofs."
- Notable find, runtime bug (quote): "It found a way to overflow the
  reference counter of a Lean object used by the kernel, corrupt the
  memory, and then prove `False`."
- Same root-cause pattern as before (quote): "The soundness bugs in
  this area were implementation mistakes, not gaps in the theory."
- Methodology, the gold standard (quote): "The gold standard is
  `comparator` and external checkers when you want to protect against
  a seriously malicious proof." — compiling ≠ verifying.
- Hardening response (quote): "We are planning to ship Lean with two
  versions of `lean4checker`: one compiled using GMP and another using
  mpn." — defense in depth, diversify implementations.
- Big picture: AI-driven adversarial proof search is now a genuine
  security concern, not hypothetical — the fix is diversified/verified
  kernels, not one-off patches.
:::

# The role of Lean in view of _AI_

## [Autoformalization of Fermat's Last Theorem (Lean FRO project)](https://lean-lang.org/use-cases/flt/)

- Years-long project led by Kevin Buzzard.

## [Autoformalization of Fermat's Last Theorem](https://www.anthropic.com/research/formalizing-fermats-last-theorem)

- Accelerated by Anthropic.
- [“Sorries are not the hard part”](https://arxiv.org/abs/2606.13925)

# [“On the Navier-Stokes Millennium Prize Problem”](https://openai.com/index/navier-stokes-solution/)

Some controversy (15th of September, ~10:30)

- [OpenAI's solutions](https://github.com/openai/NavierStokesAndEuler)
- [Tristan Buckmaster and Levent Alpöge's solution](https://github.com/tristanbuckmaster/fluid_lean)
