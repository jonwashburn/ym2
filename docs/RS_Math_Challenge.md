## Recognition Science — Standalone Advanced AI Math Challenge

Purpose: Provide a self‑contained, well‑posed set of mathematics problems derived from RS that a capable AI (or team) can attempt independently. Solutions should be rigorous, classical, and suitable for formal verification.

Submission format
- Provide precise statements, full proofs, and references to standard results used.
- Prefer constructive arguments when feasible; indicate any use of choice or classical axioms.
- If using Lean, include a Lake project pinned to mathlib; otherwise include TeX sources.

Global constants (fixed)
- φ = (1+√5)/2; J(x) = 1/2(x+1/x) − 1.

### Challenge 1: Cost Functional Uniqueness
Prove:
Let J: ℂ∖{0}→ℝ be analytic, real on ℝ_{>0}, symmetric (J(x)=J(1/x)), positive with unique minimum at x=1, and bounded J(x) ≤ K(x+1/x) on ℝ_{>0}. Then J(x)=1/2(x+1/x)−1.
Deliver: Full proof excluding higher terms and logarithmic tails; include explicit K=1/2 for this J.

### Challenge 2: Dimension Three via Link Penalty
Prove:
(a) In d=3 there exist embeddings of two disjoint simple closed curves with Lk=±1; in d≥4 any such pair is ambient‑isotopic to the unlink.
(b) Define a link cost ΔJ satisfying ΔJ ≥ ln φ·|Lk| and ΔJ=0 if unlinkable by ambient isotopy. Show that the minimal‑cost embedding forcing nonzero ΔJ occurs only in d=3.

### Challenge 3: Eight‑Tick Minimality on Q3
On the cube graph Q3, show that any closed walk visiting all vertices exactly once per period and obeying atomicity (one edge per tick) has minimal period T=8. Provide an argument excluding T∈{4,5,6,7} under atomicity.

### Challenge 4: Gap Generating Functional
Define g_m = (−1)^{m+1}/(m φ^m). Show the power series F(z)=∑_{m≥1} g_m z^m equals ln(1+z/φ) on |z|≤1, and prove absolute convergence plus a uniform tail bound. Evaluate F(1)=ln φ.

### Challenge 5: Bridge Factorization (Category‑theoretic)
Construct: A strict symmetric monoidal functor B from a program category to observables, a units quotient Q: Obs→Obs/∼, and a numeric landing Ã such that A=Ã∘Q and J=Ã∘B_*. Prove dimensionless outputs are invariant under unit anchor changes.

### Optional (bonus) Challenge 6: Born Rule and Exchange Sectors
From a path weight μ(γ)=e^{−C[γ]} with composition and phase invariance, prove P=|ψ|^2 under standard probabilistic axioms. Under particle indistinguishability, show admissible sectors reduce to 1‑D irreps, i.e. Bose or Fermi.

Acceptance criteria
- Statements are unambiguous; proofs fill all logical gaps.
- All constants (φ, ln φ, 103/(102 π^5) if used) are derived, not assumed.
- Any bridge‑level (SI) claims are deferred; only dimensionless mathematics appears.


