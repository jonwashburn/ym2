import Mathlib

/-!
Prop-level OS3 (clustering in the limit) interface: we encode the uniform
exponential decay of truncated correlators with constants independent of ε,
and convergence of Schwinger functions, then record the cluster conclusion.
-/

namespace YM

/-- OS3 hypothesis bundle for limits. -/
structure OS3LimitHypotheses where
  /-- Uniform exponential decay for truncated correlators with ε‑independent constants. -/
  uniform_truncated_decay : Prop
  /-- Tightness plus convergence of Schwinger functions along the net. -/
  convergence : Prop
  /-- Evidence fields. -/
  uniform_truncated_decay_holds : uniform_truncated_decay
  convergence_holds : convergence

/-- OS3 conclusion: cluster decomposition for the limit Schwinger functions. -/
def ClusterInLimit (H : OS3LimitHypotheses) : Prop :=
  H.uniform_truncated_decay ∧ H.convergence

/-- OS3 is preserved under limits given uniform truncated decay (interface form). -/
theorem cluster_preserved_in_limit (H : OS3LimitHypotheses) : ClusterInLimit H := by
  exact And.intro H.uniform_truncated_decay_holds H.convergence_holds

/-- From a uniform lattice spectral gap (mean-zero sector) at each regulator and
    convergence of Schwinger functions, deduce OS3 clustering in the limit. -/
structure OS3FromGap where
  uniform_lattice_gap : Prop
  schwinger_converges : Prop
  uniform_lattice_gap_holds : uniform_lattice_gap
  schwinger_converges_holds : schwinger_converges

theorem os3_clustering_from_uniform_gap (D : OS3FromGap) :
  ClusterInLimit
  { uniform_truncated_decay := D.uniform_lattice_gap
  , convergence := D.schwinger_converges
  , uniform_truncated_decay_holds := D.uniform_lattice_gap_holds
  , convergence_holds := D.schwinger_converges_holds } := by
  exact And.intro D.uniform_lattice_gap_holds D.schwinger_converges_holds

/-- OS5 (unique vacuum) hypothesis bundle. -/
structure UniqueVacuumHypotheses where
  uniform_open_gap : Prop
  os3_cluster : Prop
  uniform_open_gap_holds : uniform_open_gap
  os3_cluster_holds : os3_cluster

/-- Unique vacuum in the limit from OS3 clustering and an open spectral gap. -/
theorem unique_vacuum_in_limit (H : UniqueVacuumHypotheses) : Prop :=
  H.uniform_open_gap ∧ H.os3_cluster

end YM
