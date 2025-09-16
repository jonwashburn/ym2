## Challenge 2 — Dimension Three via Link Penalty (Solution)

Set–up (Recognition Geometry)
Let K₁, K₂ ⊂ ℝᵈ be disjoint smooth embeddings of S¹ (simple closed curves). The link cost ΔJ(K₁,K₂; d) is assumed to satisfy
\[
  \Delta J \;\ge\; (\ln \varphi)\,|\operatorname{Lk}(K_1,K_2)|,\qquad
  \Delta J=0\ \text{ if }(K_1,K_2)\ \text{is ambient–isotopic to the unlink},
\]
with \(\varphi=(1+\sqrt5)/2\) the Recognition ratio.

Result (a): Dimension test
- In d=3 there exist disjoint embeddings with Lk = ±1 (Hopf link).
- For d ≥ 4 any such pair is ambient–isotopic to the unlink.

Proof (a)
- Existence in d=3: Take a solid torus V ⊂ ℝ³. Let K₁ be its core and K₂ the boundary of a meridian disk D ⊂ V. The disk D meets K₁ transversely once, so by the Seifert surface interpretation of linking number, \(\operatorname{Lk}(K_1,K_2)=\pm 1\).
- Unlinking in d ≥ 4: For d ≥ 4 each S¹ ↪ ℝᵈ (codimension ≥ 3) is unknotted and bounds an embedded 2–disk Dᵢ; general position gives D₁ ∩ K₂ = ∅. Push K₁ across D₁ into a small circle in a ball disjoint from K₂, then do the same for K₂; the result is the unlink.

Result (b): Minimal nonzero cost occurs only in d=3
Claim. Under the link–cost rule, the least strictly positive value of ΔJ that must be paid by topology occurs only in d=3, and it is at least ln φ, attained when |Lk|=1.

Proof (b)
- For d ≥ 4: Part (a) implies every pair is ambient–isotopic to the unlink, hence ΔJ = 0 by rule — no nonzero cost is forced.
- For d = 3: Linking number is an ambient–isotopy invariant. Any embedding with |Lk| ≥ 1 cannot be unlinked; the cost rule yields
  \[ \Delta J \;\ge\; (\ln\varphi)\,|\operatorname{Lk}| \;\ge\; \ln\varphi. \]
  Thus the minimal forced nonzero cost is at least ln φ and occurs already at |Lk| = 1 (Hopf link).

Conclusion
Only in ambient dimension d=3 does topology enforce ΔJ > 0; in all d ≥ 4 the penalty can be driven to zero by ambient isotopy. Hence the least nonzero ledger increment is the single–link tax ln φ, a purely 3–dimensional effect.


